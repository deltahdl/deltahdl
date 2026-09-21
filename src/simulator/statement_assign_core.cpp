#include <cmath>
#include <cstdint>
#include <cstring>
#include <string>
#include <string_view>

#include "common/arena.h"
#include "common/types.h"
#include "elaborator/type_eval.h"
#include "parser/ast_expr.h"
#include "simulator/assoc_element.h"
#include "simulator/class_object.h"
#include "simulator/eval_array.h"
#include "simulator/eval_assoc_class_handles.h"
#include "simulator/eval_call_result.h"
#include "simulator/eval_class_array.h"
#include "simulator/eval_class_array_handles.h"
#include "simulator/eval_class_sync.h"
#include "simulator/eval_expr_internal.h"
#include "simulator/eval_function_args_scoped.h"
#include "simulator/eval_function_internal.h"
#include "simulator/eval_mailbox.h"
#include "simulator/eval_semaphore.h"
#include "simulator/eval_string.h"
#include "simulator/evaluation.h"
#include "simulator/scheduler.h"
#include "simulator/sim_context.h"
#include "simulator/statement_assign.h"
#include "simulator/statement_assign_internal.h"
#include "simulator/stmt_result.h"
#include "simulator/variable.h"

namespace delta {

// The key the kinds of the variable `lhs` names or selects into stand under
// (DeclaredKindsKey): "$unit.s" for §3.12.1's `$unit::s` (printed page 56),
// which asked by the text alone read a module's own `int s` for the string.
std::string LhsIdentName(const Expr* lhs) {
  while (lhs && lhs->kind == ExprKind::kSelect) lhs = lhs->base;
  if (lhs && lhs->kind == ExprKind::kIdentifier) return DeclaredKindsKey(lhs);
  return {};
}

void CoerceTo2State(Logic4Vec& v) {
  for (uint32_t i = 0; i < v.nwords; ++i) {
    v.words[i].aval &= ~v.words[i].bval;
    v.words[i].bval = 0;
  }
}

// A right-hand value that owns its words, for a store to keep.
//
// §6.8: "A variable is an abstraction of a data storage element. A variable
// shall store a value from one assignment to the next." Two variables are two
// storage elements, and no clause has to forbid them sharing one buffer: the
// object model the clause describes already makes them separate. EvalExpr
// answers a bare identifier with the variable's own Logic4Vec (EvalIdentifier,
// evaluation.cpp), an element select with the element variable's own vec
// (eval_select.cpp), and a Logic4Vec copies its `words` pointer rather than the
// words it points at. ResizeToWidth returns its argument untouched when the
// widths already match, so `y = x` at equal widths stored x's buffer in y.
//
// That is not a latent hazard waiting for a later write. The very next line of
// every one of these stores is `if (!var->is_4state) CoerceTo2State(...)`,
// which writes in place: on `logic [7:0] x; bit [7:0] y; y = x;` the coercion
// reached back through the alias and cleared x's own x and z bits, inside the
// statement that only read x.
//
// The copy is taken where the value is produced rather than at each store, so
// every store downstream of a production point is already safe and none of them
// has to know. A production point pays one copy for a statement; the stores are
// six, and several of them run per element.
//
// ExtractBitField copies the words -- multi-word safe, and it carries the bval
// plane, so an x or z survives the copy -- but it builds its result with
// MakeLogic4Vec, which leaves is_real, is_signed and is_string false. All three
// are read after this point and are restored beside the words:
// ConvertRealOnAssign branches on is_real to convert rather than reinterpret a
// real's bits, ResizeToWidth sign-extends on is_signed, and a value stored into
// a class property keeps its is_string for whatever later reads the property as
// text.
//
// This is the blocking mirror of SampleNbaRhs
// (statement_assign_nonblocking.cpp), which §10.4.2's sampling needed for the
// same reason.
Logic4Vec OwnRhsWords(const Logic4Vec& val, Arena& arena) {
  Logic4Vec copy = ExtractBitField(arena, val, 0, val.width);
  copy.is_real = val.is_real;
  copy.is_signed = val.is_signed;
  copy.is_string = val.is_string;
  copy.fills_width = val.fills_width;  // §5.7.1: a copy of the literal's value
  return copy;
}

void WriteVar(Variable* var, const Logic4Vec& val, Arena& arena) {
  // §10.6.2: "A force statement to a variable shall override a procedural
  // assignment ... until a release procedural statement is executed on the
  // variable." Every other writer a blocking assignment reaches declines here;
  // this one is reached only by §11.4.1's compound operators, which no case
  // asked the rule of, so `force x = 8'd50; x += 8'd10;` read 60. A force
  // establishes its own value by writing the field directly rather than through
  // this, so nothing a force or a release needs is declined.
  if (var->is_forced) return;
  var->value = ResizeToWidth(val, var->value.width, arena);
  if (!var->is_4state) CoerceTo2State(var->value);
  var->NotifyWatchers();
}

// The nearest prefix of the chain `lhs` that names stored storage -- the
// element `y[0]` under `y[0][3][1]` -- or null where no prefix short of the
// root does. §7.4.1 has an index of a packed array select a subfield and
// further indices select within it, so once the element is found every index
// past it addresses bits of that element, however many there are; only the
// one index right after the element was looked for, so a third index found
// nothing and TryResolveCompoundElement materialized a fresh variable under the
// chain's full name, which nothing read back. A prefix whose index carries x or
// z has no name to look up and is passed over, and the empty window
// SelectStorageBits resolves for it then leaves the write with no effect.
static Variable* DeepestElementPrefix(const Expr* lhs, SimContext& ctx,
                                      Arena& arena) {
  for (const Expr* p = lhs->base; p != nullptr && p->kind == ExprKind::kSelect;
       p = p->base) {
    std::string name;
    if (!BuildCompoundLhsName(p, ctx, arena, name)) continue;
    if (auto* var = ctx.FindVariable(name)) return var;
  }
  return nullptr;
}

// §7.4.4: the variable a chain of two or more indices on a packed
// multidimensional variable stands on -- `x` for `x[1][3]` on a
// `logic [1:0][7:0] x` -- or null where `root` is not one. A name registered
// as a queue or an associative array holds its elements in an object of its own
// rather than in the variable under the name (§7.10, §7.8), so an index of it
// names a whole element and is declined here for the writers that reach those.
static Variable* PackedRootVariable(std::string_view root, SimContext& ctx) {
  if (ctx.FindQueue(root) != nullptr || ctx.FindAssocArray(root) != nullptr)
    return nullptr;
  auto* var = ctx.FindVariable(root);
  return (var != nullptr && var->packed_elem_width > 1) ? var : nullptr;
}

// §11.5.1: the object a packed sub-select of an unpacked array element stands
// on. `logic [7:0] mem [0:3]` stores each element under its own indexed name,
// so `mem[0][3]` is a bit-select of the eight-bit element `mem[0]` and not a
// second array dimension: the clause makes an index of a packed object address
// a bit of it, and only the flat name of a genuinely multidimensional array is
// an element in its own right. Answers the element the trailing indices select
// within -- `y[0]` for `y[0][3][1]` on a `logic [3:0][7:0] y[1:0]` as much as
// for `y[0][3]`, §7.4.1 making the second index a subfield and the third a bit
// of it -- or the packed variable itself where the chain stands on one with no
// unpacked dimension, `x` for `x[1][3]`; null where the name is of neither
// shape.
//
// The two are told apart by the flat name: `A[1][2]` on an `int A[2][3]` is a
// variable, made when the array's leaves were created, and this declines it, so
// the writers below go on treating a real element as one. Where the flat name
// names nothing and a prefix does, the trailing indices have an object to be
// bits of, and where no prefix does the index addresses nothing at all --
// §7.4.5's no operation, which TryResolveCompoundElement answers.
//
// The read side already draws the line here: TryCompoundArraySelect
// (eval_select.cpp) declines the same shape so EvalSelect reads the trailing
// indices as selects within the element it evaluates.
Variable* TryResolveCompoundElementBase(const Expr* lhs, SimContext& ctx,
                                        Arena& arena) {
  if (lhs->kind != ExprKind::kSelect || lhs->base == nullptr) return nullptr;
  if (lhs->base->kind != ExprKind::kSelect) return nullptr;
  std::string compound;
  if (BuildCompoundLhsName(lhs, ctx, arena, compound) &&
      ctx.FindVariable(compound) != nullptr) {
    return nullptr;
  }
  std::string_view root = CompoundRootName(lhs);
  const ArrayInfo* info = ctx.FindArrayInfo(root);
  if (info == nullptr) return PackedRootVariable(root, ctx);
  // §7.4.4 also has dimensions "defined in stages with typedef", and only the
  // range the declaration itself wrote is recorded: `typedef bsix mem_type
  // [0:3]; mem_type ba [0:7];` leaves one dimension known, so `ba[0]` is a leaf
  // of that dimension and `ba[0][0]` is the second dimension the record does
  // not have rather than a bit of a packed object. The two names have the same
  // shape, and what tells them apart is whether the element type stands for an
  // array, which the elaborated tables do not yet say -- #3598. Until they do,
  // an element type written as a name is left to the element the writer below
  // materializes, and an element type that is an integral type of its own is a
  // packed object whose bits this addresses.
  if (info->elem_type_kind == DataTypeKind::kNamed) return nullptr;
  return DeepestElementPrefix(lhs, ctx, arena);
}

// §7.4.4: writes `rhs_val` to the element a multidimensional indexed name such
// as `a[i][j]` stands for. Answers true when the name is one of that shape --
// whether it wrote the element or performed §7.4.5's no operation for an index
// the array does not hold -- so the caller does not go on to the writers below
// it, which would take the name down to the array's base carrier.
static bool TryCompoundElementWrite(const Expr* lhs, const Logic4Vec& rhs_val,
                                    SimContext& ctx, Arena& arena) {
  // §11.5.1: `mem[0][3] = 1'b1` on a `logic [7:0] mem [0:3]` selects a bit of
  // the element mem[0], which is a packed object of its own. Read as a second
  // array dimension it named an element that does not exist, and the fallback
  // below the caller walks such a name down to the array's base carrier, so the
  // bit reached neither. WriteBitSelect resolves every index past the element
  // through SelectStorageBits, so `y[0][3][1]` and `y[0][3][7:4]` on a
  // `logic [3:0][7:0] y[1:0]` land in subfield 3 of `y[0]` (§7.4.1).
  if (auto* elem = TryResolveCompoundElementBase(lhs, ctx, arena)) {
    WriteBitSelect(elem, lhs, rhs_val, ctx, arena);
    return true;
  }
  bool absent_element = false;
  if (auto* compound =
          TryResolveCompoundElement(lhs, ctx, arena, &absent_element)) {
    WriteVar(compound, rhs_val, arena);
    return true;
  }
  return absent_element;
}

// §11.5.1: `c.p[7:0] = v` targets bits of a class property, which lives in
// the object's property map rather than in a variable, so no writer of
// TrySelectBlockingAssign can reach it and ResolveLhsVariable answers null
// for the name it rebuilds. §7.4.6: `c.a[2] = v`, or `a[2] = v` in a method,
// targets an element of a class property declared as an array, held on the
// object one by one.
static bool TryWriteClassPropertyPart(const Expr* lhs, Logic4Vec& rhs_val,
                                      SimContext& ctx, Arena& arena) {
  return TryWriteClassArrayElement(lhs, rhs_val, ctx, arena) ||
         TryWriteClassPropertyBits(lhs, rhs_val, ctx, arena);
}

// §6.16: `s[i] = c` on a string variable replaces one character of its text,
// or nothing for an unknown index, and is done either way.
static bool TryWriteStringVariableChar(Variable* var, const Expr* lhs,
                                       const Logic4Vec& rhs_val,
                                       SimContext& ctx, Arena& arena) {
  if (!var || lhs->kind != ExprKind::kSelect || !lhs->base || lhs->index_end)
    return false;
  auto base_name = LhsIdentName(lhs->base);
  if (base_name.empty() || !ctx.IsStringVariable(base_name)) return false;
  auto idx_val = EvalExpr(lhs->index, ctx, arena);
  if (!HasUnknownBits(idx_val)) {
    StringWriteByte(var, static_cast<uint32_t>(idx_val.ToUint64()),
                    static_cast<uint8_t>(rhs_val.ToUint64() & 0xFF), arena);
    var->NotifyWatchers();
  }
  return true;
}

bool TrySelectBlockingAssign(const Expr* lhs, Logic4Vec& rhs_val,
                             SimContext& ctx, Arena& arena) {
  if (auto* elem = TryResolveArrayElement(lhs, ctx)) {
    WriteVar(elem, rhs_val, arena);
    return true;
  }
  if (TryQueueIndexedWrite(lhs, rhs_val, ctx, arena)) return true;
  if (TryAssocIndexedWrite(lhs, rhs_val, ctx, arena)) return true;
  // §7.8.7: `aa[3][7:0] = v` targets bits of an associative array element, so
  // the element is allocated and written. TryResolveCompoundElement below
  // would otherwise fabricate a plain variable named "aa[3]" and divert the
  // write into it, leaving the array untouched.
  if (TryWriteAssocElementBits(lhs, rhs_val, ctx, arena)) return true;
  // §6.16: `h.p[0] = "x"` on a string property replaces one character of its
  // text. TryWriteClassPropertyPart declines a property of no declared width
  // and the writers below it name no storage of a class object, so the write
  // was dropped with `true` returned, as a bit-select of a property once was.
  if (TryWriteStringPropertyChar(lhs, rhs_val, ctx, arena)) return true;
  if (TryWriteClassPropertyPart(lhs, rhs_val, ctx, arena)) return true;
  if (TryCompoundElementWrite(lhs, rhs_val, ctx, arena)) return true;
  auto* var = ResolveLhsVariable(lhs, ctx);
  if (TryWriteStringVariableChar(var, lhs, rhs_val, ctx, arena)) return true;
  if (var) {
    WriteBitSelect(var, lhs, rhs_val, ctx, arena);
  }
  return true;
}

static Logic4Vec ConvertToRealIfNeeded(double d, uint32_t target_width,
                                       Arena& arena) {
  if (target_width == 32) {
    auto f = static_cast<float>(d);
    uint32_t fbits = 0;
    std::memcpy(&fbits, &f, sizeof(float));
    auto result = MakeLogic4VecVal(arena, 32, fbits);
    result.is_real = true;
    return result;
  }
  uint64_t dbits = 0;
  std::memcpy(&dbits, &d, sizeof(double));
  auto result = MakeLogic4VecVal(arena, 64, dbits);
  result.is_real = true;
  return result;
}

Logic4Vec ConvertRealForKnownLhs(Logic4Vec rhs_val, bool lhs_is_real,
                                 uint32_t target_width, Arena& arena) {
  // §6.12.1: a real assigned to an integer converts by rounding to the nearest
  // integer with ties away from zero (std::llround), never a raw bit copy.
  if (rhs_val.is_real && !lhs_is_real) {
    double d = RealVecToDouble(rhs_val);
    auto ival = static_cast<uint64_t>(static_cast<int64_t>(std::llround(d)));
    auto result = MakeLogic4VecVal(arena, target_width, ival);
    result.is_signed = true;
    return result;
  }
  // §6.12.1: an expression assigned to a real converts numerically; x/z bits of
  // the source read as zero (ToUint64's aval & ~bval projection).
  if (!rhs_val.is_real && lhs_is_real) {
    uint64_t raw = rhs_val.nwords > 0
                       ? (rhs_val.words[0].aval & ~rhs_val.words[0].bval)
                       : 0;
    auto d = static_cast<double>(raw);
    return ConvertToRealIfNeeded(d, target_width, arena);
  }
  if (rhs_val.is_real && lhs_is_real && rhs_val.width != target_width) {
    double d = RealVecToDouble(rhs_val);
    return ConvertToRealIfNeeded(d, target_width, arena);
  }
  return ResizeToWidth(rhs_val, target_width, arena);
}

Logic4Vec ConvertRealOnAssign(Logic4Vec rhs_val, const Expr* lhs,
                              const Variable& var, SimContext& ctx,
                              Arena& arena) {
  uint32_t target_width = var.value.width;
  auto name = LhsIdentName(lhs);
  if (name.empty()) return ResizeToWidth(rhs_val, target_width, arena);
  bool lhs_is_real = var.is_real || ctx.IsRealVariable(name);
  return ConvertRealForKnownLhs(rhs_val, lhs_is_real, target_width, arena);
}

// Whether `lhs` names a string variable, whose whole value the assignment
// takes rather than a window sized to the variable: a bare or selected name
// registered as a string, or §26.3's `P::ps`, a package's string held under
// the "P.ps" key the lowerer registered it by. Sized to the variable, the
// package string kept the first four characters of "name2" and lost the rest.
static bool IsStringTarget(const Expr* lhs, SimContext& ctx) {
  auto name = LhsIdentName(lhs);
  if (!name.empty()) return ctx.IsStringVariable(name);
  if (lhs->kind != ExprKind::kMemberAccess || !lhs->is_scope_resolution ||
      lhs->lhs == nullptr || lhs->rhs == nullptr ||
      lhs->lhs->kind != ExprKind::kIdentifier ||
      lhs->rhs->kind != ExprKind::kIdentifier) {
    return false;
  }
  return ctx.IsStringVariable(std::string(lhs->lhs->text) + "." +
                              std::string(lhs->rhs->text));
}

void AssignToScalarLhs(const Stmt* stmt, Logic4Vec rhs_val, SimContext& ctx,
                       Arena& arena) {
  auto* var = ResolveLhsVariable(stmt->lhs, ctx);
  if (var) {
    if (var->is_forced) return;

    if (IsStringTarget(stmt->lhs, ctx)) {
      var->value = StripStringZeros(rhs_val, arena);
      var->NotifyWatchers();
      return;
    }
    rhs_val = ConvertRealOnAssign(rhs_val, stmt->lhs, *var, ctx, arena);
    var->value = rhs_val;
    if (!var->is_4state) CoerceTo2State(var->value);
    var->NotifyWatchers();

    // §11.9 with §23.9: the tag is recorded under the key the target's
    // storage was created by (TagKeyOfName), the one a declaration
    // initializer's tag already stands under, so both forms name one tag. The
    // tag table keeps the view it is given, so the key is interned in the
    // arena rather than left in a string that ends with this statement.
    if (stmt->rhs && stmt->rhs->kind == ExprKind::kTagged && stmt->rhs->rhs) {
      ctx.SetVariableTag(
          *arena.Create<std::string>(TagKeyOfName(stmt->lhs->text, ctx)),
          stmt->rhs->rhs->text);
    }
  } else if (stmt->lhs->kind == ExprKind::kMemberAccess) {
    WriteStructField(stmt->lhs, rhs_val, ctx);
  }
}

// §6.18: assignment between named event variables. `e = null` nullifies the
// event; `e1 = e2` (both events) aliases the lhs to the rhs trigger.
static bool TryEventVarAssign(const Stmt* stmt, SimContext& ctx) {
  if (stmt->lhs->kind != ExprKind::kIdentifier || !stmt->rhs ||
      stmt->rhs->kind != ExprKind::kIdentifier) {
    return false;
  }
  auto* lhs_var = ctx.FindVariable(stmt->lhs->text);
  if (!lhs_var || !lhs_var->is_event) return false;

  if (stmt->rhs->text == "null") {
    ctx.NullifyEventVariable(stmt->lhs->text);
    return true;
  }
  auto* rhs_var = ctx.FindVariable(stmt->rhs->text);
  if (rhs_var && rhs_var->is_event) {
    ctx.AliasVariable(stmt->lhs->text, stmt->rhs->text);
    return true;
  }
  return false;
}

// §7.5.1/§7.10/§8.4: an assignment that sizes or rebuilds an array object,
// or constructs an object into an element, rather than writing a value:
// `new[]` to a dynamic array property, `new` to an element of an array
// property of class handles or of a declared associative array of them
// (§7.8), or any assignment to a queue.
static bool TryArrayObjectAssign(const Stmt* stmt, SimContext& ctx,
                                 Arena& arena) {
  return TryClassArrayNewAssign(stmt, ctx, arena) ||
         TryClassArrayElementNewAssign(stmt, ctx, arena) ||
         TryAssocElementNewAssign(stmt, ctx, arena) ||
         TryQueueBlockingAssign(stmt, ctx, arena);
}

// §15.3 and §15.4: `new` into a semaphore or a mailbox, or a handle copied
// into a class property, one arm of the dispatch below (complexity 15).
static bool TryDispatchSyncAssign(const Stmt* stmt, SimContext& ctx,
                                  Arena& arena) {
  return TrySemaphoreNewAssign(stmt, ctx, arena) ||
         TryMailboxNewAssign(stmt, ctx, arena) ||
         TrySyncHandleAssign(stmt, ctx, arena);
}

// Run the chain of special-case blocking-assignment handlers that do not need
// the generic rhs value (class `new`, a semaphore or mailbox handle into a
// property, associative-array copy/literal, streaming-to-queue,
// dynamic-array/queue/event/slice/subarray, and compound operators). Returns
// true when one of them fully handled the assignment. A §25.9 virtual interface
// takes the generic store: it is a value, the handle of the instance it
// represents, which an interface instance name, another virtual interface and
// `null` each evaluate to (EvalIdentifier in evaluation.cpp), so no arm has to
// bind it.
bool TryDispatchSpecialBlockingAssign(const Stmt* stmt, SimContext& ctx,
                                      Arena& arena) {
  if (TryDispatchSyncAssign(stmt, ctx, arena)) return true;
  if (TryClassNewAssign(stmt, ctx, arena)) return true;
  if (TryTypedClassNewAssign(stmt, ctx, arena)) return true;
  if (TryMemberClassNewAssign(stmt, ctx, arena)) return true;
  if (TryAssocMapAssign(stmt, ctx, arena)) return true;
  if (TryAssocCopyAssign(stmt, ctx)) return true;
  if (TryAssocLiteralAssign(stmt, ctx, arena)) return true;
  if (TryStreamingConcatToQueueTarget(stmt, ctx, arena)) return true;
  if (TryArrayObjectAssign(stmt, ctx, arena)) return true;
  if (TryEventVarAssign(stmt, ctx)) return true;
  if (TryUnpackedSliceAssign(stmt, ctx, arena)) return true;
  if (TrySubarrayAssign(stmt, ctx, arena)) return true;
  // A bare `lhs op= rhs` statement carries the compound operator as its own rhs
  // node. A parenthesized compound assign is instead an embedded assignment
  // expression (11.4.1 primary `( operator_assignment )`), e.g. `x = (y += 2)`,
  // whose target is its own lhs (y), not the statement lhs (x); let it fall
  // through to the generic path so EvalExpr routes it to EvalCompoundAssign.
  if (stmt->rhs && stmt->rhs->kind == ExprKind::kBinary &&
      IsCompoundAssignOp(stmt->rhs->op) && !stmt->rhs->is_parenthesized) {
    ApplyCompoundAssignOp(stmt, ctx, arena);
    return true;
  }
  return false;
}

// Apply the generic blocking assignment of `rhs_val` once the special-case
// handlers have declined. Covers concatenation/pattern unpack, streaming
// unpack, bit/part-select writes, array writes, and the scalar fallback.
void ApplyGenericBlockingAssign(const Stmt* stmt, Logic4Vec rhs_val,
                                SimContext& ctx, Arena& arena) {
  // §10.9: a typed assignment pattern expression (type'{...}) is also a valid
  // left-hand target, and TryUnpackConcatLhs strips the type prefix so its
  // members unpack the RHS exactly as a bare positional pattern does.
  if (TryUnpackConcatLhs(stmt->lhs, rhs_val, ctx, arena)) return;
  if (stmt->lhs->kind == ExprKind::kStreamingConcat) {
    UnpackStreamingConcatLhs(stmt->lhs, rhs_val, ctx, arena);
    return;
  }
  rhs_val = ApplyStreamPackToTargetWidening(stmt, rhs_val, ctx, arena);
  if (stmt->lhs->kind == ExprKind::kSelect) {
    TrySelectBlockingAssign(stmt->lhs, rhs_val, ctx, arena);
    return;
  }
  if (TryArrayBlockingAssign(stmt, ctx, arena)) return;
  AssignToScalarLhs(stmt, rhs_val, ctx, arena);
}

StmtResult ExecBlockingAssignImpl(const Stmt* stmt, SimContext& ctx,
                                  Arena& arena) {
  if (!stmt->lhs) return StmtResult::kDone;
  if (TryDispatchSpecialBlockingAssign(stmt, ctx, arena))
    return StmtResult::kDone;
  // §7.3.2 with §11.9: a call's result reaches a tagged union target with the
  // tag its body returned, which the store below reads off no call.
  auto rhs_val = EvalRhsCarryingReturnedTag(stmt, ctx, arena);
  // Every generic blocking store -- the scalar write, the select writers,
  // WriteStructField and the class property behind it -- takes the value from
  // here, so one copy at the point it is produced covers all of them.
  rhs_val = OwnRhsWords(rhs_val, arena);
  ApplyGenericBlockingAssign(stmt, rhs_val, ctx, arena);
  return StmtResult::kDone;
}

void PerformBlockingAssign(const Expr* lhs, const Logic4Vec& rhs_val,
                           SimContext& ctx, Arena& arena) {
  if (!lhs) return;
  // The value arrives already made, from a caller outside this file -- an
  // embedded assignment expression, a continuous assignment's driven value, an
  // output argument's writeback, a DPI or system task's result. This entry is
  // where such a value is produced as far as the store path can see, so it is
  // copied once here rather than in the arms below.
  Logic4Vec owned = OwnRhsWords(rhs_val, arena);
  // §10.9: a typed assignment pattern expression on the left unpacks like the
  // bare pattern it wraps.
  if (TryUnpackConcatLhs(lhs, owned, ctx, arena)) return;

  if (lhs->kind == ExprKind::kStreamingConcat) {
    UnpackStreamingConcatLhs(lhs, owned, ctx, arena);
    return;
  }
  if (lhs->kind == ExprKind::kSelect) {
    TrySelectBlockingAssign(lhs, owned, ctx, arena);
    return;
  }
  auto* var = ResolveLhsVariable(lhs, ctx);
  if (var) {
    if (var->is_forced) return;
    auto converted = ConvertRealOnAssign(owned, lhs, *var, ctx, arena);
    var->value = converted;
    if (!var->is_4state) CoerceTo2State(var->value);
    var->NotifyWatchers();
  } else if (lhs->kind == ExprKind::kMemberAccess) {
    WriteStructField(lhs, owned, ctx);
  } else if (lhs->kind == ExprKind::kIdentifier) {
    // §8.11: inside a method a bare name no variable answers is a property of
    // the object the method runs on, and §13.5.2's copy-out of an output
    // argument names one whenever a method passes its own property as the
    // actual -- `get(vif)` from a method of the class declaring `vif`. Left to
    // the two arms above, the value went nowhere.
    TryFuncClassPropertyWrite(lhs, owned, ctx, arena);
  }
}

}  // namespace delta
