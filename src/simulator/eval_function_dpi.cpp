#include <cstddef>
#include <cstdint>
#include <cstring>
#include <string>
#include <vector>

#include "common/arena.h"
#include "common/types.h"
#include "parser/ast.h"
#include "simulator/dpi_runtime.h"
#include "simulator/eval_function_internal.h"
#include "simulator/evaluation.h"
#include "simulator/sim_context.h"
#include "simulator/statement_assign.h"
#include "simulator/svdpi.h"

namespace delta {

namespace {

int ResolveDpiActualIndex(const DpiRtFunction* import, const Expr* expr,
                          size_t i, size_t positional_count) {
  if (i < positional_count) {
    return static_cast<int>(i);
  }
  for (size_t j = 0; j < expr->arg_names.size(); ++j) {
    if (expr->arg_names[j] == import->args[i].name) {
      return static_cast<int>(positional_count + j);
    }
  }
  return -1;
}

// §35.5.5 lists the types an imported function's result may have and §35.5.6
// the types its formals may have; this is the width each carries. Built at a
// fixed width instead, a longint or a chandle result lost its upper half and a
// byte arrived padded with bits its type does not have. A void result falls to
// the default with everything else the clauses do not name: §35.5.5 gives such
// a call no value, so nothing reads what width it came out at.
uint32_t DpiValueWidth(DataTypeKind kind) {
  switch (kind) {
    case DataTypeKind::kBit:
    case DataTypeKind::kLogic:
    case DataTypeKind::kReg:
      return 1;
    case DataTypeKind::kByte:
      return 8;
    case DataTypeKind::kShortint:
      return 16;
    case DataTypeKind::kLongint:
    case DataTypeKind::kChandle:
    case DataTypeKind::kTime:
    case DataTypeKind::kReal:
    case DataTypeKind::kShortreal:
    case DataTypeKind::kRealtime:
      return 64;
    default:
      return 32;
  }
}

bool IsRealKind(DataTypeKind kind) {
  return kind == DataTypeKind::kReal || kind == DataTypeKind::kShortreal ||
         kind == DataTypeKind::kRealtime;
}

// §35.2.2.1: "The implementation (representation and layout) of 4-state values
// ... is irrelevant for SystemVerilog semantics and can only impact the foreign
// side of the interface." A four-state scalar crosses in the sv_0/sv_1/sv_z/
// sv_x encoding svdpi.h names, which is what the aval/bval pair of bit 0 says:
// a clear bval selects 0 or 1, a set one selects z or x. Carried as one word
// per bit instead, a design's x came back 1 and its z came back 0.
SvLogic SvLogicOfWord(Logic4Word w) {
  bool one = (w.aval & 1U) != 0;
  if ((w.bval & 1U) == 0) {
    return static_cast<SvLogic>(one ? sv_1 : sv_0);
  }
  return static_cast<SvLogic>(one ? sv_x : sv_z);
}

Logic4Word WordOfSvLogic(SvLogic v) {
  switch (v) {
    case sv_0:
      return Logic4Word{0, 0};
    case sv_1:
      return Logic4Word{1, 0};
    case sv_z:
      return Logic4Word{0, 1};
    default:
      return Logic4Word{1, 1};
  }
}

// §35.2.2: a chandle is "capable of holding a pointer value", and a design
// holds that pointer as the bits of its variable. The pointer is rebuilt out of
// those bits rather than cast into being, so the handle the foreign side handed
// out is the handle it gets back when the design passes it in again.
SvChandle ChandleOfWord(Logic4Word w) {
  SvChandle handle = nullptr;
  auto bits = static_cast<uintptr_t>(w.aval);
  std::memcpy(&handle, &bits, sizeof(handle));
  return handle;
}

// The value a design's expression presents to a formal (or a call's result to
// the expression it stands in), typed as the declaration types it. §35.6.1 has
// the crossing go through a temporary of the formal's type, so the type the
// declaration names is the one the value is built at; DpiRuntime then coerces
// between that and the foreign side.
DpiArgValue DpiArgValueOfType(DataTypeKind kind, const Logic4Vec& v) {
  Logic4Word word = v.nwords == 0 ? Logic4Word{} : v.words[0];
  DpiArgValue out;
  switch (kind) {
    case DataTypeKind::kReal:
    case DataTypeKind::kShortreal:
    case DataTypeKind::kRealtime:
      out = DpiArgValue::FromReal(v.is_real ? RealVecToDouble(v)
                                            : static_cast<double>(word.aval));
      out.type = kind;
      return out;
    case DataTypeKind::kChandle:
      return DpiArgValue::FromChandle(ChandleOfWord(word));
    case DataTypeKind::kBit:
      return DpiArgValue::FromBit(static_cast<SvBit>(word.aval & 1U));
    case DataTypeKind::kLogic:
    case DataTypeKind::kReg:
      out = DpiArgValue::FromLogic(SvLogicOfWord(word));
      out.type = kind;
      return out;
    case DataTypeKind::kInteger:
      return DpiArgValue::FromLogicVec(SvLogicVecVal{
          static_cast<uint32_t>(word.aval), static_cast<uint32_t>(word.bval)});
    case DataTypeKind::kString:
      // §35.5.6 admits a string formal, whose value lives outside the aval/bval
      // pair a Logic4Vec carries. Nothing lowers a design's string into one
      // yet, so the crossing yields the empty string rather than a reading of
      // bits that do not hold one.
      return DpiArgValue::FromString("");
    default:
      // Every remaining integral type -- byte, shortint, int, and whatever a
      // declaration left at DpiArg's own default -- narrows and sign-extends
      // through §35.6.1's coercion rather than through a cast written here.
      return CoerceArgValue(
          DpiArgValue::FromLongint(static_cast<int64_t>(word.aval)), kind);
  }
}

// A value of the declared type carrying what crossed the boundary, unknown bits
// included. A real is carried as its own bit pattern in a 64-bit vector marked
// is_real, which is the shape MakeRealVec in src/simulator/evaluation.cpp
// builds and what the rest of the evaluator reads a real out of.
Logic4Vec DpiValueOfType(Arena& arena, DataTypeKind kind,
                         const DpiArgValue& value) {
  uint32_t width = DpiValueWidth(kind);
  if (IsRealKind(kind)) return MakeRealVec(arena, value.AsReal(), width);

  Logic4Word word;
  switch (kind) {
    case DataTypeKind::kChandle:
      word.aval =
          static_cast<uint64_t>(reinterpret_cast<uintptr_t>(value.AsChandle()));
      break;
    case DataTypeKind::kBit:
      word.aval = value.AsBit() & 1U;
      break;
    case DataTypeKind::kLogic:
    case DataTypeKind::kReg:
      word = WordOfSvLogic(value.AsLogic());
      break;
    case DataTypeKind::kInteger:
      word.aval = value.AsLogicVec().aval;
      word.bval = value.AsLogicVec().bval;
      break;
    case DataTypeKind::kString:
      break;
    case DataTypeKind::kLongint:
    case DataTypeKind::kTime:
      word.aval = static_cast<uint64_t>(value.AsLongint());
      break;
    default:
      word.aval = static_cast<uint64_t>(static_cast<int64_t>(value.AsInt()));
      break;
  }

  Logic4Vec v = MakeLogic4Vec(arena, width);
  uint64_t mask = width >= 64 ? ~0ULL : ((1ULL << width) - 1);
  v.words[0].aval = word.aval & mask;
  v.words[0].bval = word.bval & mask;
  return v;
}

DpiArgValue EvalDpiActualForFormal(const DpiRtFunction* import, size_t i,
                                   const ActualBindingCtx& b) {
  DataTypeKind type = import->args[i].type;
  // The actual is evaluated whatever the formal's direction is, an output
  // included: §35.5.1.2 keeps the value from reaching the foreign function --
  // DpiRuntime::CallImportWithArgs seeds an output formal with the undetermined
  // value instead -- while §35.6.2 needs the value the actual held before the
  // call to say afterwards whether the call changed it.
  int ai = ResolveDpiActualIndex(import, b.call, i, b.positional_count);
  if (ai >= 0 && b.call->args[static_cast<size_t>(ai)] != nullptr) {
    return DpiArgValueOfType(
        type, EvalExpr(b.call->args[static_cast<size_t>(ai)], b.ctx, b.arena));
  }
  if (import->args[i].default_value) {
    return DpiArgValueOfType(
        type, EvalExpr(import->args[i].default_value, b.ctx, b.arena));
  }
  // A formal the call bound nothing to and the declaration gave no default has
  // no value to present, so it presents the type's own undetermined value.
  return DpiRuntime::UndeterminedOutputValue(type);
}

std::vector<DpiArgValue> BindDpiActualsFromImport(const DpiRtFunction* import,
                                                  const ActualBindingCtx& b) {
  std::vector<DpiArgValue> args;
  args.reserve(import->args.size());
  for (size_t i = 0; i < import->args.size(); ++i) {
    args.push_back(EvalDpiActualForFormal(import, i, b));
  }
  return args;
}

std::vector<DpiArgValue> BindDpiActualsPositional(const ActualBindingCtx& b) {
  std::vector<DpiArgValue> args;
  args.reserve(b.call->args.size());
  for (auto* arg : b.call->args) {
    // With no formal to read a type off, the value crosses as the type DpiArg
    // itself declares when a declaration says nothing.
    args.push_back(
        DpiArgValueOfType(DataTypeKind::kInt, EvalExpr(arg, b.ctx, b.arena)));
  }
  return args;
}

std::vector<DpiArgValue> BindDpiCallActuals(const DpiRtFunction* import,
                                            const ActualBindingCtx& b) {
  if (!import->args.empty()) return BindDpiActualsFromImport(import, b);
  return BindDpiActualsPositional(b);
}

// §35.6.2: the value changes of an imported function's output and inout
// arguments are handled once control has returned, by propagating each as if
// the actual were assigned the formal immediately after the return. `changes`
// names the actuals the call altered, in declaration order, so an actual the
// call left as it found it is assigned nothing and propagates nothing.
// §13.5.2 has WritebackOutputArgs in eval_function_args.cpp do the equivalent
// for a native subroutine, reading the values out of the callee's local
// variables; a foreign callee has none, so the values are read out of the
// vector it was called with.
void WritebackDpiChangedArgs(const DpiRtFunction* import,
                             const ActualBindingCtx& b,
                             const std::vector<DpiArgValue>& actuals,
                             const std::vector<DpiArgValueChange>& changes) {
  for (const auto& change : changes) {
    size_t i = change.index;
    if (i >= import->args.size() || i >= actuals.size()) continue;
    int ai = ResolveDpiActualIndex(import, b.call, i, b.positional_count);
    if (ai < 0) continue;
    // The value arrives at the width the formal declares, unknown bits and
    // all, and the assignment narrows it to whatever the actual holds, as an
    // assignment to that actual would anywhere else.
    PerformBlockingAssign(
        b.call->args[static_cast<size_t>(ai)],
        DpiValueOfType(b.arena, import->args[i].type, actuals[i]), b.ctx,
        b.arena);
  }
}

}  // namespace

Logic4Vec EvalDpiCall(const Expr* expr, SimContext& ctx, Arena& arena) {
  auto* dpi = ctx.GetDpiRuntime();
  const DpiRtFunction* import =
      dpi == nullptr ? nullptr : dpi->FindImport(expr->callee);
  if (import == nullptr) return MakeLogic4VecVal(arena, 1, 0);
  // §35.6: calling an imported function uses the same usage and syntax as a
  // native function call. When the import's formals are known, resolve the
  // call-site actuals against them so that named-argument binding and omitted
  // arguments backed by defaults behave exactly as for native subroutine calls.
  ActualBindingCtx binding{expr, expr->args.size() - expr->arg_names.size(),
                           ctx, arena};
  std::vector<DpiArgValue> args = BindDpiCallActuals(import, binding);

  // §35.5.3: "A DPI call chain is a call chain ... that begins when
  // SystemVerilog code calls an imported subroutine." This call site is that
  // beginning, and the frame's context property is the one the import's own
  // declaration carries (§35.5.1.3). The declaration's instantiated scope is
  // not carried here: a design's import declarations do not yet reach the
  // registry at all, which is #3285, and the scope arrives with them.
  dpi->EnterDeclaredImportCall(expr->callee, DpiScope{});

  DpiArgValue result;
  if (import->is_pure) {
    // §35.5.2: a pure function's call "can be ... replaced with the value
    // previously computed for the same values of the input arguments", and a
    // pure function has no output or inout formals for a copy-back to carry.
    result = dpi->CallImportReusingPureResult(expr->callee, args);
  } else {
    // §35.5.1.2 and §35.6.1 copy the written formals back into the actuals;
    // §35.6.2 says which of those actuals the call actually changed.
    std::vector<DpiArgValueChange> changes;
    result = dpi->CallImportDetectingChanges(expr->callee, args, changes);
    WritebackDpiChangedArgs(import, binding, args, changes);
  }

  // §35.9 item c): an imported function returning while a disable is in effect
  // shall have acknowledged it first, and a simulator checks that on the
  // return. Leaving the frame is that return.
  dpi->LeaveImportCall();

  // §35.6.1: the result crosses back through a temporary of the declared result
  // type, so a body that computed it in another type is coerced to the type
  // §35.5.5 says the call site receives.
  return DpiValueOfType(arena, import->return_type,
                        CoerceArgValue(result, import->return_type));
}

}  // namespace delta
