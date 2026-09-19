#ifndef VPI_USER_H
#define VPI_USER_H

// §36.7: the include file a PLI application writes to reach the VPI. "The
// libraries of PLI functions are defined in C include files, which are a
// normative part of this standard. These files also define constants,
// structures, and other data used by the library of PLI routines and the
// interface mechanisms. These files are vpi_user.h (listed in Annex K) and
// sv_vpi_user.h (listed in Annex M). PLI applications that use the VPI routines
// shall include these files."
//
// This file is the one every translation unit that reaches the VPI includes,
// under the name the clause gives it. Until 2026-09-18 the tool's own code
// reached the same declarations through simulator/vpi.h, a one-line alias of
// this file, and an application following the clause to the letter found
// nothing under `#include "vpi_user.h"`; the alias is gone and the clause's
// name is the only spelling.
//
// The two files divide the interface rather than repeating it, and each annex
// says where its own half stops: Annex K reserves the constant values 1 through
// 299 "for use in this vpi_user.h file", Annex M reserves 600 through 999 for
// the SystemVerilog extensions. simulator/sv_vpi_user.h includes this file, so
// an application that names only the SV half still has the base library under
// it, which is what makes §36.7's "shall include these files" satisfiable by
// naming either one.
//
// The tool's own VPI types arrive with the interface. delta::VpiContext and the
// model helpers are no part of what Annex K lists and an application has no use
// for them; they are here because the PLI spellings in vpi_user_macros.h are
// aliases of those C++ types rather than structures of their own, which is a
// fact about how this tool realizes the interface rather than about the clause.
//
// §36.12.2.1 puts the compatibility mechanism in this file: "When a mode is
// selected by one of the means above, C-preprocessor constructs in vpi_user.h
// cause the following VPI functions to be redefined to mode-specific versions",
// and "a compilation error will occur during the processing of vpi_user.h if
// more than one of the preceding symbols is defined". The constructs live in
// simulator/vpi_compatibility.h and were reached by nothing an application
// includes, so the clause's own example -- define the symbol, include
// vpi_user.h -- selected a mode and got no redefinition at all. The header is
// read here, ahead of the declarations it renames, which is the whole of what
// makes the selection take effect.
//
// §K.2 opens the file with its portability help -- the sized integer types,
// and the macros that say how a symbol is imported, exported or marked
// external -- and closes it by undefining the macros the file defined for
// itself, so that a translation unit sees them only inside the file and keeps
// any it had defined before the include. simulator/vpi_portability.h is that
// opening, which simulator/vpi_user_macros.h reads ahead of the declarations
// it writes with what the opening defines; the closing is at the end of this
// file.
//
// Do not reorder the includes - each depends on types the ones above it
// declare, and the PLI typedefs and macros come last, after the delta::
// declarations they alias.
//
// The IWYU pragma marks the includes as this file's exports: Annex K makes
// every declaration below part of vpi_user.h, and the sub-headers are only how
// this repository stores that one file. clang-tidy's misc-include-cleaner,
// which otherwise asks each translation unit to include the header that
// declares each symbol it uses, reads the pragma and counts this file as
// providing them.

// IWYU pragma: begin_exports
#include "simulator/vpi_compatibility.h"
#include "simulator/vpi_constants.h"
#include "simulator/vpi_context.h"
#include "simulator/vpi_data_structs.h"
#include "simulator/vpi_model_helpers1.h"
#include "simulator/vpi_model_helpers2.h"
#include "simulator/vpi_model_helpers3.h"
#include "simulator/vpi_object.h"
#include "simulator/vpi_portability.h"
#include "simulator/vpi_user_macros.h"
// IWYU pragma: end_exports

// §K.2: the file ends by taking back the portability macros it defined for
// itself. PLI_EXTERN and PLI_VEXTERN go unconditionally; the two DLL
// specifications go only where simulator/vpi_portability.h defined them, which
// the VPI_USER_DEFINED_ pair records; and the prototype macros go with the
// PLI_PROTOTYPES that marked them.
#undef PLI_EXTERN
#undef PLI_VEXTERN

#ifdef VPI_USER_DEFINED_DLLISPEC
#undef VPI_USER_DEFINED_DLLISPEC
#undef PLI_DLLISPEC
#endif
#ifdef VPI_USER_DEFINED_DLLESPEC
#undef VPI_USER_DEFINED_DLLESPEC
#undef PLI_DLLESPEC
#endif

#ifdef PLI_PROTOTYPES
#undef PLI_PROTOTYPES
#undef PROTO_PARAMS
#undef XXTERN
#undef EETERN
#endif

#endif /* VPI_USER_H */
