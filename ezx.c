/* ezx.c: Routines for reading EmuZWin .ezx snapshots (read only)
   Copyright (c) 2026 XJ

   This program is free software; you can redistribute it and/or modify
   it under the terms of the GNU General Public License as published by
   the Free Software Foundation; either version 2 of the License, or
   (at your option) any later version.

   This program is distributed in the hope that it will be useful,
   but WITHOUT ANY WARRANTY; without even the implied warranty of
   MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
   GNU General Public License for more details.

   You should have received a copy of the GNU General Public License along
   with this program; if not, write to the Free Software Foundation, Inc.,
   51 Franklin Street, Fifth Floor, Boston, MA 02110-1301 USA.

   Format: EZXFormat_Eng.htm by Vladimir Kladov (EmuZWin 2.7 package).
   Plain file starts with "Emuz"; compressed one with "EZX", a 32-bit
   compressed length and a UCL NRV2E (8-bit) stream of the plain file.
*/

#include "config.h"

#include <string.h>

#include "internals.h"

#define EZX_BANK 0x4000
#define EZX_MAX_UNPACKED ( 16 * 1024 * 1024 )

/* Offsets inside the fixed TSpecData record */
#define EZX_OFS_ROM0   4
#define EZX_OFS_RAM    ( EZX_OFS_ROM0 + 2 * EZX_BANK )
#define EZX_OFS_LOCK   ( EZX_OFS_RAM + 8 * EZX_BANK )
#define EZX_OFS_REGS   ( EZX_OFS_LOCK + 1 )
#define EZX_OFS_I      ( EZX_OFS_REGS + 24 )
#define EZX_OFS_TACTS  ( EZX_OFS_I + 7 )
#define EZX_OFS_BANKS  ( EZX_OFS_TACTS + 4 )
#define EZX_OFS_AY     ( EZX_OFS_BANKS + 8 )
#define EZX_FIXED_LEN  ( EZX_OFS_AY + 17 + 4 + 30 )

/* ---- UCL NRV2E decompressor, 8-bit bit buffer ---- */

typedef struct ezx_bits {
  const libspectrum_byte *src;
  size_t pos, len;
  unsigned int bb, n;
  int error;
} ezx_bits;

static int
ezx_getbit( ezx_bits *s )
{
  if( !s->n ) {
    if( s->pos >= s->len ) { s->error = 1; return 0; }
    s->bb = s->src[ s->pos++ ];
    s->n = 8;
  }
  s->n--;
  return ( s->bb >> s->n ) & 1;
}

static libspectrum_byte
ezx_getbyte( ezx_bits *s )
{
  if( s->pos >= s->len ) { s->error = 1; return 0; }
  return s->src[ s->pos++ ];
}

static int
ezx_put( libspectrum_byte **dst, size_t *olen, size_t *osize,
         libspectrum_byte b )
{
  if( *olen >= *osize ) {
    if( *osize >= EZX_MAX_UNPACKED ) return 1;
    *osize *= 2;
    *dst = libspectrum_renew( libspectrum_byte, *dst, *osize );
  }
  (*dst)[ (*olen)++ ] = b;
  return 0;
}

static libspectrum_error
ezx_nrv2e( const libspectrum_byte *src, size_t len,
           libspectrum_byte **out, size_t *out_len )
{
  ezx_bits s = { src, 0, len, 0, 0, 0 };
  size_t osize = 256 * 1024, olen = 0;
  libspectrum_dword m_off, m_len, last_m_off = 1;
  libspectrum_byte *dst = libspectrum_new( libspectrum_byte, osize );

  for( ;; ) {
    while( ezx_getbit( &s ) ) {
      if( s.error || ezx_put( &dst, &olen, &osize, ezx_getbyte( &s ) ) )
        goto fail;
    }
    if( s.error ) goto fail;

    m_off = 1;
    for( ;; ) {
      m_off = m_off * 2 + ezx_getbit( &s );
      if( ezx_getbit( &s ) ) break;
      m_off = ( m_off - 1 ) * 2 + ezx_getbit( &s );
      if( s.error ) goto fail;
    }

    if( m_off == 2 ) {
      m_off = last_m_off;
      m_len = ezx_getbit( &s );
    } else {
      m_off = ( m_off - 3 ) * 256 + ezx_getbyte( &s );
      if( m_off == 0xffffffffUL ) break;   /* end marker */
      m_len = ( m_off ^ 0xffffffffUL ) & 1;
      m_off >>= 1;
      last_m_off = ++m_off;
    }

    if( m_len ) {
      m_len = 1 + ezx_getbit( &s );
    } else if( ezx_getbit( &s ) ) {
      m_len = 3 + ezx_getbit( &s );
    } else {
      m_len++;
      do {
        m_len = m_len * 2 + ezx_getbit( &s );
        if( s.error ) goto fail;
      } while( !ezx_getbit( &s ) );
      m_len += 3;
    }
    m_len += ( m_off > 0x500 );
    if( s.error || m_off > olen ) goto fail;

    for( m_len++; m_len; m_len-- ) {
      if( ezx_put( &dst, &olen, &osize, dst[ olen - m_off ] ) ) goto fail;
    }
  }

  *out = dst;
  *out_len = olen;
  return LIBSPECTRUM_ERROR_NONE;

fail:
  libspectrum_free( dst );
  libspectrum_print_error( LIBSPECTRUM_ERROR_CORRUPT,
                           "libspectrum_ezx_read: corrupt compressed data" );
  return LIBSPECTRUM_ERROR_CORRUPT;
}

/* ---- snapshot ---- */

static libspectrum_word
ezx_word( const libspectrum_byte *p )
{
  return p[0] | ( p[1] << 8 );
}

static libspectrum_dword
ezx_dword( const libspectrum_byte *p )
{
  return p[0] | ( p[1] << 8 ) | ( p[2] << 16 ) | ( (libspectrum_dword)p[3] << 24 );
}

/* Machine from Lock7FFD and the frame length in the 'MULT' chunk */
static libspectrum_machine
ezx_machine( const libspectrum_byte *d, size_t len )
{
  size_t p = EZX_FIXED_LEN;
  libspectrum_dword frame = 0;

  if( d[ EZX_OFS_LOCK ] ) return LIBSPECTRUM_MACHINE_48;

  while( p + 8 <= len ) {
    libspectrum_dword chunk_len = ezx_dword( d + p + 4 );
    if( !memcmp( d + p, "MULT", 4 ) && chunk_len >= 9 && p + 8 + 9 <= len )
      frame = ezx_dword( d + p + 8 + 5 );
    if( chunk_len > len - p - 8 ) break;
    p += 8 + chunk_len;
  }

  if( frame >= 71000 ) return LIBSPECTRUM_MACHINE_PENT;
  return LIBSPECTRUM_MACHINE_128;
}

static libspectrum_error
ezx_read_plain( libspectrum_snap *snap, const libspectrum_byte *d, size_t len )
{
  const libspectrum_byte *r = d + EZX_OFS_REGS;
  const libspectrum_byte *b = d + EZX_OFS_BANKS;
  libspectrum_machine machine;
  libspectrum_byte port7ffd;
  int i;

  if( len < EZX_FIXED_LEN ) {
    libspectrum_print_error( LIBSPECTRUM_ERROR_CORRUPT,
                             "libspectrum_ezx_read: file too short" );
    return LIBSPECTRUM_ERROR_CORRUPT;
  }

  machine = ezx_machine( d, len );
  libspectrum_snap_set_machine( snap, machine );

  libspectrum_snap_set_a  ( snap, r[1] ); libspectrum_snap_set_f  ( snap, r[0] );
  libspectrum_snap_set_bc ( snap, ezx_word( r +  2 ) );
  libspectrum_snap_set_de ( snap, ezx_word( r +  4 ) );
  libspectrum_snap_set_hl ( snap, ezx_word( r +  6 ) );
  libspectrum_snap_set_ix ( snap, ezx_word( r +  8 ) );
  libspectrum_snap_set_iy ( snap, ezx_word( r + 10 ) );
  libspectrum_snap_set_a_ ( snap, r[13] ); libspectrum_snap_set_f_ ( snap, r[12] );
  libspectrum_snap_set_bc_( snap, ezx_word( r + 14 ) );
  libspectrum_snap_set_de_( snap, ezx_word( r + 16 ) );
  libspectrum_snap_set_hl_( snap, ezx_word( r + 18 ) );
  libspectrum_snap_set_pc ( snap, ezx_word( r + 20 ) );
  libspectrum_snap_set_sp ( snap, ezx_word( r + 22 ) );

  r = d + EZX_OFS_I;
  libspectrum_snap_set_i   ( snap, r[0] );
  libspectrum_snap_set_r   ( snap, r[1] );
  libspectrum_snap_set_iff1( snap, r[3] ? 1 : 0 );
  libspectrum_snap_set_iff2( snap, r[4] ? 1 : 0 );
  libspectrum_snap_set_im  ( snap, r[6] & 3 );
  libspectrum_snap_set_tstates( snap, ezx_dword( d + EZX_OFS_TACTS ) );

  /* b[0] ROM at 0000 (0=128, 1=48, 2=TR-DOS), b[1] RAM at C000,
     b[2] video (1=bank 7), b[3] border, b[5] just after EI */
  libspectrum_snap_set_out_ula( snap, b[3] & 0x07 );
  libspectrum_snap_set_last_instruction_ei( snap, b[5] ? 1 : 0 );

  port7ffd = ( b[1] & 0x07 ) | ( b[2] ? 0x08 : 0 ) |
             ( b[0] == 0 ? 0 : 0x10 ) | ( d[ EZX_OFS_LOCK ] ? 0x20 : 0 );
  libspectrum_snap_set_out_128_memoryport( snap, port7ffd );

  if( b[0] == 2 && machine == LIBSPECTRUM_MACHINE_PENT ) {
    libspectrum_snap_set_beta_active( snap, 1 );
    libspectrum_snap_set_beta_paged( snap, 1 );
  }

  libspectrum_snap_set_out_ay_registerport( snap, d[ EZX_OFS_AY ] & 0x0f );
  for( i = 0; i < 16; i++ )
    libspectrum_snap_set_ay_registers( snap, i, d[ EZX_OFS_AY + 1 + i ] );

  for( i = 0; i < 8; i++ ) {
    libspectrum_byte *ram;
    if( machine == LIBSPECTRUM_MACHINE_48 && i != 0 && i != 2 && i != 5 )
      continue;
    ram = libspectrum_new( libspectrum_byte, EZX_BANK );
    memcpy( ram, d + EZX_OFS_RAM + i * EZX_BANK, EZX_BANK );
    libspectrum_snap_set_pages( snap, i, ram );
  }

  return LIBSPECTRUM_ERROR_NONE;
}

libspectrum_error
libspectrum_ezx_read( libspectrum_snap *snap, const libspectrum_byte *buffer,
                      size_t length )
{
  libspectrum_byte *plain = NULL;
  size_t plain_len = 0, packed_len;
  libspectrum_error error;

  if( length >= 4 && !memcmp( buffer, "Emuz", 4 ) )
    return ezx_read_plain( snap, buffer, length );

  if( length < 7 || memcmp( buffer, "EZX", 3 ) ) {
    libspectrum_print_error( LIBSPECTRUM_ERROR_SIGNATURE,
                             "libspectrum_ezx_read: not an EZX file" );
    return LIBSPECTRUM_ERROR_SIGNATURE;
  }

  packed_len = ezx_dword( buffer + 3 );
  if( packed_len > length - 7 ) packed_len = length - 7;

  error = ezx_nrv2e( buffer + 7, packed_len, &plain, &plain_len );
  if( error ) return error;

  if( plain_len < 4 || memcmp( plain, "Emuz", 4 ) ) {
    libspectrum_free( plain );
    libspectrum_print_error( LIBSPECTRUM_ERROR_CORRUPT,
                             "libspectrum_ezx_read: bad unpacked signature" );
    return LIBSPECTRUM_ERROR_CORRUPT;
  }

  error = ezx_read_plain( snap, plain, plain_len );
  libspectrum_free( plain );
  return error;
}
