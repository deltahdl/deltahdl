#pragma once

#include <cstdint>
#include <string_view>
#include <vector>

#include "common/source_loc.h"
#include "elaborator/rtlir_scopes.h"
#include "parser/ast_expr.h"
#include "parser/ast_module.h"
#include "parser/ast_specify.h"

namespace delta {

// The elaborated forms of the two primitives no continuous assignment can
// stand for, a bidirectional pass switch (§28.8) and an instance of a
// user-defined primitive (§29.8), which RtlirModule holds beside its
// continuous assignments. Moved out of rtlir.h, which stood at the size the
// assert-no-oversized-source-files job fails at.

// §28.8: one bidirectional pass switch -- tran, rtran, or a tranif0, tranif1,
// rtranif0 or rtranif1 -- between two bidirectional terminals, with the
// control terminal and the turn-on and turn-off delays of the enabled forms.
// Unlike every other gate it drives neither terminal from the other, so it is
// no continuous assignment: the run joins the two nets it connects while it
// conducts.
struct RtlirBidirSwitch {
  GateKind kind = GateKind::kTran;
  Expr* terminal_a = nullptr;
  Expr* terminal_b = nullptr;
  Expr* control = nullptr;
  Expr* turn_on_delay = nullptr;
  Expr* turn_off_delay = nullptr;
};

// §29.8: one instance of a user-defined primitive, and what drives its output
// terminal. A gate instance lowers to an RtlirContAssign carrying a synthesized
// expression, and a primitive instance cannot, for two reasons. §29.3.4 defines
// the output as a table lookup rather than an operator, and §29.5 gives a
// sequential primitive a current state which "is considered equivalent to the
// current output value" and which an expression has nowhere to keep. So the
// instance carries the declaration it names, and the simulator evaluates that
// declaration's table against the input terminals, holding one UdpEvalState per
// instance for the length of the run.
//
// The terminals are split the way §29.8 writes them -- "udp_instance ::= [
// name_of_instance ] ( output_terminal , input_terminal { , input_terminal } )"
// -- so `inputs` already stands in the order UdpEvalState indexes a table row
// by, and nothing downstream has to work out which terminal is the output.
//
// Two delays and no third, because §29.8 rules that "Only two delays may be
// specified because z is not supported for UDPs". RtlirContAssign carries a
// third for the switches that need one.
struct RtlirUdpInst {
  const UdpDecl* decl = nullptr;
  // §29.8: "The instance name is optional, just as for gates." Empty where the
  // source wrote none, which is why it cannot be what identifies the instance.
  std::string_view name;
  // Where the primitive's name stands, which is the position a report about
  // this instance carries.
  SourceLoc loc;
  Expr* output = nullptr;
  std::vector<Expr*> inputs;
  uint8_t drive_strength0 = 0;
  uint8_t drive_strength1 = 0;
  Expr* delay = nullptr;
  Expr* delay_fall = nullptr;
  GenBlockConsts gen_block_consts;
  GenBlockPrefixes gen_block_prefixes;
};

}  // namespace delta
