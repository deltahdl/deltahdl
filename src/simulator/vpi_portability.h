#pragma once

// §K.2, the portability help of vpi_user.h: the macros the annex writes its
// routine declarations and its one global variable with, so that an
// application or a tool can select, ahead of the include, how a symbol is
// imported or exported on a platform that marks such things. Each is defined
// only where nothing defined it first, which is what lets a definition made
// before the include stand.
//
// The sized integer types the same section fixes are in vpi_pli_types.h,
// which this header reads first for the same reason the annex puts them
// first: PLI_INT32 and its siblings are what every declaration below the
// portability help is written in.
//
// vpi_user.h undefines PLI_EXTERN, PLI_VEXTERN and, where this header rather
// than the includer defined them, the two DLL specifications and the
// prototype macros, at its end as §K.2 does; so a translation unit sees
// them only between the two ends of that file, and a definition it made
// itself before the include is left where it was.

#include "simulator/vpi_pli_types.h"

/* Use to import a symbol */

#if (defined(_MSC_VER) || defined(__MINGW32__) || defined(__CYGWIN__))
#ifndef PLI_DLLISPEC
#define PLI_DLLISPEC __declspec(dllimport)
#define VPI_USER_DEFINED_DLLISPEC 1
#endif
#else
#ifndef PLI_DLLISPEC
#define PLI_DLLISPEC
#endif
#endif

/* Use to export a symbol */

#if (defined(_MSC_VER) || defined(__MINGW32__) || defined(__CYGWIN__))
#ifndef PLI_DLLESPEC
#define PLI_DLLESPEC __declspec(dllexport)
#define VPI_USER_DEFINED_DLLESPEC 1
#endif
#else
#ifndef PLI_DLLESPEC
#define PLI_DLLESPEC
#endif
#endif

/* Use to mark a function as external */

#ifndef PLI_EXTERN
#define PLI_EXTERN
#endif

/* Use to mark a variable as external */

#ifndef PLI_VEXTERN
#define PLI_VEXTERN extern
#endif

#ifndef PLI_PROTOTYPES
#define PLI_PROTOTYPES
#define PROTO_PARAMS(params) params

/* object is defined imported by the application */

#define XXTERN PLI_EXTERN PLI_DLLISPEC

/* object is exported by the application */

#define EETERN PLI_EXTERN PLI_DLLESPEC
#endif
