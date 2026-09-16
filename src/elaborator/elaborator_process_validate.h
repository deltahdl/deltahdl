#pragma once

#include "common/diagnostic.h"
#include "elaborator/rtlir.h"
#include "parser/ast.h"

namespace delta {

// §9.2.2.1 to §9.2.2.4 and §9.2.3: the rules on the statements a procedure of
// each kind may hold and on its event control, read off the process built
// for `item`: an always with no timing control, an always_comb or
// always_latch with an explicit event control, a timing control or a
// fork-join, the latch an always_comb infers and the combinational body an
// always_latch has, an always_ff without an event control, with a timing
// control, a fork-join or no edge, and a final procedure with a timing
// control or a fork-join. Defined in elaborator_process_validate.cpp.
void ValidateProcess(RtlirProcessKind kind, ModuleItem* item,
                     const RtlirProcess& proc, DiagEngine& diag);

}  // namespace delta
