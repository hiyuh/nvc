//
//  Copyright (C) 2011-2012  Nick Gasson
//
//  This program is free software: you can redistribute it and/or modify
//  it under the terms of the GNU General Public License as published by
//  the Free Software Foundation, either version 3 of the License, or
//  (at your option) any later version.
//
//  This program is distributed in the hope that it will be useful,
//  but WITHOUT ANY WARRANTY; without even the implied warranty of
//  MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
//  GNU General Public License for more details.
//
//  You should have received a copy of the GNU General Public License
//  along with this program.  If not, see <http://www.gnu.org/licenses/>.
//

#ifndef _LOC_H
#define _LOC_H

#include <stdint.h>

typedef struct loc {
   uint16_t   first_line;
   uint16_t   first_column;
   uint16_t   last_line;
   uint16_t   last_column;
   const char *file;
   const char *linebuf;
} loc_t;

#define LINE_INVALID   UINT16_MAX
#define COLUMN_INVALID UINT16_MAX

static const loc_t LOC_INVALID = {
   LINE_INVALID,
   COLUMN_INVALID,
   LINE_INVALID,
   COLUMN_INVALID,
   NULL,
   NULL
};

#endif  // _LOC_H
