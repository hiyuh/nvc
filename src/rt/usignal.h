//
//  Copyright (C) 2011  Nick Gasson
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

#ifndef INC_RT_USIGNAL_H
#define INC_RT_USIGNAL_H

// Fixed fields in user signal structure
enum {
   USIGNAL_RESOLVED,
   USIGNAL_LAST_VALUE,
   USIGNAL_DECL,
   USIGNAL_FLAGS,
   USIGNAL_N_SOURCES,
   USIGNAL_OFFSET,
   USIGNAL_SOURCES,
   USIGNAL_SENSITIVE,
   USIGNAL_EVENT_CB,

   USIGNAL_N_FIELDS
};

// User signal flags
enum {
   USIGNAL_F_ACTIVE = (1 << 0),
   USIGNAL_F_EVENT  = (1 << 1),
   USIGNAL_F_UPDATE = (1 << 2)
};

#endif // RT_USIGNAL_H
