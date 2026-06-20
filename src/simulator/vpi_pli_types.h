#pragma once

#include <cstdint>

// §K.2: the vpi_user.h portability layer fixes the width of the integer types
// every VPI routine and structure is expressed in. These aliases are the
// DeltaHDL realization of those typedefs. They live in the global namespace
// because the PLI/VPI C API names them globally, and are kept in this small
// standalone header so headers that are pulled in early (e.g. vpi_context.h,
// included before vpi_user_macros.h by vpi.h) can name them.
using PLI_INT32 = int32_t;
using PLI_UINT32 = uint32_t;
using PLI_INT64 = int64_t;
using PLI_UINT64 = uint64_t;
using PLI_INT16 = short;
using PLI_UINT16 = unsigned short;
using PLI_BYTE8 = char;
using PLI_UBYTE8 = unsigned char;
