#include <cstdint>
#include <cstring>
#include <string>
#include <string_view>

#include "common/arena.h"
#include "common/types.h"
#include "elaborator/const_eval.h"
#include "elaborator/rtlir.h"
#include "parser/ast_type.h"
#include "simulator/eval_function_internal.h"
#include "simulator/eval_string.h"
#include "simulator/evaluation.h"
#include "simulator/lowerer.h"
#include "simulator/lowerer_register.h"
#include "simulator/sim_context.h"
#include "simulator/variable.h"
#include "simulator/vcd_dump_state.h"

namespace delta {

void Lowerer::LowerParams(const RtlirModule* mod) {
  for (const auto& p : mod->params) {
    // §23.10/§6.20: a parameter is an instance-specific runtime value, so its
    // variable is scoped by the instance prefix (empty for a top module). This
    // makes a child instance's parameters — including any defparam override —
    // visible to that instance's processes. The name is arena-persisted because
    // SimContext keys variables by string_view.
    auto* full = arena_.Create<std::string>(inst_prefix_ + std::string(p.name));
    // §21.7.2.1: dumped, the parameter is declared with the parameter var_type.
    ctx_.Vcd().MarkVcdParameter(*full);
    LowerParam(p, *full);
  }
}

// §6.20.1 (printed page 124) with §6.20.2: a parameter declared with unpacked
// dimensions is an array of values, assigned by an assignment pattern, so it
// is given the element variables and the ArrayInfo CreateArrayElements
// (lowerer_var.cpp) gives a module's array variable, under the parameter's own
// key, each element filled from the pattern by §10.9.1's rules. The value fold
// takes no pattern and leaves such a parameter unresolved, which left it no
// storage at all and every element reading x.
static void CreateParamArray(const RtlirParamDecl& p, std::string_view full,
                             SimContext& ctx, Arena& arena) {
  ParamStorageShape shape = ParamStorageShapeOf(p);
  const DataType& type = *p.decl_type;
  RtlirVariable var;
  var.name = p.name;
  var.width = shape.width;
  var.is_signed = shape.is_signed;
  var.is_4state = DeclaredTypeIs4State(type, ctx);
  var.is_real = DeclaredTypeIsReal(type, ctx);
  var.dtype = &type;
  var.elem_type_kind = type.kind;
  var.init_expr = p.default_value;
  var.unpacked_dims = p.unpacked_bounds;
  for (const auto& dim : p.unpacked_bounds) {
    var.unpacked_dim_sizes.push_back(dim.Size());
  }
  const RtlirUnpackedDim& outer = p.unpacked_bounds.front();
  var.unpacked_lo = outer.Low();
  var.unpacked_size = outer.Size();
  var.is_descending = outer.left > outer.right;
  var.num_unpacked_dims = static_cast<uint32_t>(p.unpacked_bounds.size());
  CreateArrayElements(full, var, ctx, arena);
}

void Lowerer::LowerParam(const RtlirParamDecl& p, std::string_view full) {
  if (p.is_unbounded) {
    ctx_.RegisterUnboundedParam(full);
    ctx_.CreateVariable(full, 32);
    return;
  }
  if (!p.unpacked_bounds.empty()) {
    CreateParamArray(p, full, ctx_, arena_);
    return;
  }
  if (!p.is_resolved) return;
  // §6.20.2: a parameter declared real holds a real value, so it is lowered
  // the way a real variable is -- the double's bit pattern in 64 bits, marked
  // real and registered as one. Everything that reads a real reads it from
  // that mark, so without it the same 64 bits are taken for the integer they
  // spell.
  if (p.is_real_value) {
    auto* rvar = ctx_.CreateVariable(full, 64);
    uint64_t bits = 0;
    std::memcpy(&bits, &p.resolved_real, sizeof(bits));
    rvar->value = MakeLogic4VecVal(arena_, 64, bits);
    rvar->value.is_real = true;
    rvar->is_real = true;
    ctx_.RegisterRealVariable(full);
    return;
  }
  // §6.16: a parameter declared string holds a value of arbitrary length, and
  // the subclause rules that for it "no truncation occurs". Neither half of
  // the lowering below can honour that. EvalTypeWidth gives kString no width,
  // so decl_width is 0 and the fallback takes 32, keeping four characters of
  // the ten in §6.16's own example `parameter string default_name = "John
  // Smith"`; and resolved_value is 64 bits, which is why the characters are
  // read from resolved_string instead. StringToLogic4Vec packs one byte per
  // character with the leftmost character in the most significant byte, and
  // StripStringZeros drops the "\0" §6.16 forbids a string to contain,
  // leaving a value exactly as wide as the characters need. Registering the
  // variable as a string is the same second half the real arm above has,
  // because what reads a string reads SimContext::IsStringVariable rather
  // than the width.
  //
  // An overridden parameter is read here too, because is_string_value being
  // set says resolved_string holds the value the parameter has now rather
  // than the one it was declared with. ApplyParamOverride records the
  // characters for §23.10.2's two instance forms and for a configuration, on
  // a parameter whose is_string_value is still clear and whose declared
  // initializer Elaborator::ElaborateParamPortList then withholds; an
  // override that is not a string literal therefore leaves the flag clear.
  // Elaborator::ApplyDefparams records them for §23.10.1's defparam, where
  // the declaration's own characters are already recorded by then, so it
  // clears the flag itself when the right-hand side is not a string literal.
  if (p.is_string_value) {
    auto chars =
        StripStringZeros(StringToLogic4Vec(arena_, p.resolved_string), arena_);
    auto* svar = ctx_.CreateVariable(full, chars.width);
    svar->value = chars;
    ctx_.RegisterStringVariable(full);
    // §21.7.5: Table 21-11 gives string no row, and §21.7.2.3 rules that a
    // $var's size "specifies how many bits are in the variable", which no
    // size states for a value whose length §6.16 lets vary. SimContext
    // decides that by the declared kind, so without this the parameter is
    // dumped with a $var size that follows its character count.
    ctx_.Vcd().SetVcdVarKind(full, DataTypeKind::kString);
    return;
  }
  ParamStorageShape shape = ParamStorageShapeOf(p);
  uint32_t width = shape.width;
  auto* var = ctx_.CreateVariable(full, width);
  var->value =
      MakeLogic4VecVal(arena_, width, static_cast<uint64_t>(p.resolved_value));
  // §6.20.2: a value wider than 64 bits is re-evaluated whole from its own
  // expression, the folded value holding the low word alone, as is one
  // whose expression holds an x or a z (§5.7.1), which the fold holds as 0.
  ReevaluateParamValue(p, var, ctx_, arena_);
  // §11.8.2: an operand is sign-extended to the propagated width only when it
  // is signed, so a parameter declared signed, or an untyped one whose final
  // value is (§6.20.2), has to reach evaluation carrying that. Without it
  // `parameter signed [3:0] P = -4'sd1` reads back as 15.
  var->is_signed = shape.is_signed;
  var->value.is_signed = shape.is_signed;
}

}  // namespace delta
