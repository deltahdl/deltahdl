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
// The name is the whole of what this file adds. Every declaration below was
// already compiled into the tool and already reachable, under the repository's
// own spelling simulator/vpi.h, so what an application following the clause to
// the letter was missing was not the library but the file the clause tells it
// to include: a `#include "vpi_user.h"` found nothing, and the one file of the
// two that did exist, simulator/sv_vpi_user.h, opened by including
// simulator/vpi.h rather than the base file Annex M has it include.
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
// Do not reorder the includes - each depends on types the ones above it
// declare, and the PLI typedefs and macros come last, after the delta::
// declarations they alias.

#include "simulator/vpi_compatibility.h"
#include "simulator/vpi_constants.h"
#include "simulator/vpi_context.h"
#include "simulator/vpi_data_structs.h"
#include "simulator/vpi_model_helpers1.h"
#include "simulator/vpi_model_helpers2.h"
#include "simulator/vpi_model_helpers3.h"
#include "simulator/vpi_object.h"
#include "simulator/vpi_user_macros.h"

#endif
