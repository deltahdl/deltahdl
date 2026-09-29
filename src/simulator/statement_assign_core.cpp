#include <algorithm>
#include <cmath>
#include <cstddef>
#include <cstdint>
#include <cstring>
#include <optional>
#include <string>
#include <string_view>
#include <vector>

#include "common/arena.h"
#include "common/types.h"
#include "elaborator/type_eval.h"
#include "parser/ast_expr.h"
#include "simulator/assoc_element.h"
#include "simulator/class_object.h"
#include "simulator/eval_array.h"
#include "simulator/eval_array_class_assoc.h"
#include "simulator/eval_assoc_class_handles.h"
#include "simulator/eval_call_result.h"
#include "simulator/eval_class_array.h"
#include "simulator/eval_class_array_handles.h"
#include "simulator/eval_class_sync.h"
#include "simulator/eval_expr_internal.h"
#include "simulator/eval_function_args_scoped.h"
#include "simulator/eval_function_internal.h"
#include "simulator/eval_mailbox.h"
#include "simulator/eval_member_path.h"
#include "simulator/eval_semaphore.h"
#include "simulator/eval_string.h"
#include "simulator/evaluation.h"
#include "simulator/scheduler.h"
#include "simulator/sim_context.h"
#include "simulator/sim_context_types.h"
#include "simulator/statement_assign.h"
#include "simulator/statement_assign_internal.h"
#include "simulator/stmt_result.h"
#include "simulator/struct_string_member.h"
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
  // §6.16: a string has no declared width, so a string variable -- an element
  // of a fixed-size array of strings among them -- takes the whole text rather
  // than the width of whatever was written to it first.
  var->value = var->is_string ? StripStringZeros(val, arena)
                              : ResizeToWidth(val, var->value.width, arena);
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
  return TryWriteClassArrayElementChar(lhs, rhs_val, ctx, arena) ||
         TryWriteClassArrayElementBits(lhs, rhs_val, ctx, arena) ||
         TryWriteClassArrayElement(lhs, rhs_val, ctx, arena) ||
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

// §6.16 with §7.4: an element of an array of strings is a string, so `sa[0][1]
// = "X"` replaces character 1 of the element `sa[0]`, or nothing for an
// unknown index, and is done either way. Taken as a select of the element's
// bits (TryCompoundElementWrite), it wrote bit 1 of the text. §7.4.4: an
// element of a multidimensional array, `m[1][0]` in `m[1][0][0] = "P"`, is
// its own leaf variable (TryResolveCompoundElement).
//
// Only a declared array of strings is looked into, known by its name before
// any element is resolved: TryResolveCompoundElement makes the variable a
// chain names where it finds none, so asked of `y[0][3]` on a `logic
// [3:0][7:0] y[1:0]`, whose third index is a packed one, it made one, and the
// bit-select that followed wrote that instead of the element.
static bool DeclaredArrayOfStrings(const Expr* sel, SimContext& ctx) {
  const Expr* root = sel;
  while (root != nullptr && root->kind == ExprKind::kSelect) root = root->base;
  if (root == nullptr || root->kind != ExprKind::kIdentifier) return false;
  const ArrayInfo* info = ctx.FindArrayInfo(root->text);
  if (info == nullptr) return false;
  if (info->elem_type_kind == DataTypeKind::kString) return true;
  std::string first(root->text);
  if (info->dim_los.empty()) {
    first += "[" + std::to_string(info->lo) + "]";
  } else {
    for (uint32_t lo : info->dim_los) first += "[" + std::to_string(lo) + "]";
  }
  return ctx.IsStringVariable(first);
}

static bool TryWriteStringElementChar(const Expr* lhs, const Logic4Vec& rhs_val,
                                      SimContext& ctx, Arena& arena) {
  if (lhs->kind != ExprKind::kSelect || lhs->base == nullptr ||
      lhs->index_end != nullptr || lhs->base->kind != ExprKind::kSelect ||
      !DeclaredArrayOfStrings(lhs->base, ctx))
    return false;
  Variable* element = TryResolveArrayElement(lhs->base, ctx);
  if (element == nullptr)
    element = TryResolveCompoundElement(lhs->base, ctx, arena, nullptr);
  if (element == nullptr || !element->is_string) return false;
  Logic4Vec idx_val = EvalExpr(lhs->index, ctx, arena);
  if (!HasUnknownBits(idx_val)) {
    StringWriteByte(element, static_cast<uint32_t>(idx_val.ToUint64()),
                    static_cast<uint8_t>(rhs_val.ToUint64() & 0xFF), arena);
    element->NotifyWatchers();
  }
  return true;
}

// §7.2 with §7.4.2: `m.v[1] = 20` writes one element of an unpacked array
// member, its window of the structure's bits, leaving the rest; an index
// outside the member writes nothing.
static bool TryStructArrayMemberWrite(const Expr* lhs, const Logic4Vec& rhs_val,
                                      SimContext& ctx, Arena& arena) {
  StructArrayElementRef ref;
  if (!ResolveStructArrayElement(lhs, ctx, arena, ref)) return false;
  if (!ref.in_range || (ref.var != nullptr && ref.var->is_forced)) return true;
  DepositBitField(*ref.value, ref.bit_offset,
                  ResizeToWidth(rhs_val, ref.width, arena), ref.width);
  if (ref.var != nullptr) ref.var->NotifyWatchers();
  return true;
}

// The element `select` names, `layout_width` bits wide, as a member write
// finds it: its value where the container holds it, and for an associative
// entry that does not exist yet the value §7.8.7 allocates it with, the
// element type's default or initial value (AssocAllocValue) -- its members'
// declared defaults among them -- rather than the nonexistent-entry value a
// read would answer with its warning.
static Logic4Vec ElementBeforeMemberWrite(const Expr* select,
                                          uint32_t layout_width,
                                          SimContext& ctx, Arena& arena) {
  const AssocArrayObject* aa = FindAssocArrayOfBase(select->base, ctx, arena);
  if (aa != nullptr) {
    Logic4Vec key = EvalExpr(select->index, ctx, arena);
    bool held =
        aa->is_string_key
            ? aa->str_data.count(AssocStringKey(key)) != 0
            : !HasUnknownBits(key) && aa->int_data.count(AssocIntKey(
                                          key, aa->is_wildcard, aa->index_width,
                                          aa->is_index_signed)) != 0;
    if (!held)
      return OwnRhsWords(
          ResizeToWidth(AssocAllocValue(aa, arena), layout_width, arena),
          arena);
  }
  return OwnRhsWords(
      ResizeToWidth(EvalExpr(select, ctx, arena), layout_width, arena), arena);
}

// §7.2 with §7.5, §7.8 and §7.10: `d[1].a = 11` writes a member of the
// structure an element of a dynamic, associative or queue container holds, a
// variable or a class property: the element is read, the member's bits set in
// it, and the element written back as `d[1] = ...` writes it, which allocates
// an associative entry the key names no element of yet. Built into a name,
// `d[1]` named no variable and the write went nowhere.
static bool TryContainerElementMemberWrite(const Expr* lhs,
                                           const Logic4Vec& rhs_val,
                                           SimContext& ctx, Arena& arena) {
  if (lhs->kind != ExprKind::kMemberAccess || lhs->lhs == nullptr ||
      lhs->lhs->kind != ExprKind::kSelect || lhs->lhs->index_end != nullptr ||
      lhs->rhs == nullptr || lhs->rhs->kind != ExprKind::kIdentifier)
    return false;
  const Expr* select = lhs->lhs;
  const StructTypeInfo* layout = ContainerElementLayout(select->base, ctx);
  if (layout == nullptr) return false;
  uint32_t offset = 0;
  const StructFieldInfo* field =
      ResolveStructField(layout, lhs->rhs->text, &offset);
  if (field == nullptr) return false;
  Logic4Vec element =
      ElementBeforeMemberWrite(select, layout->total_width, ctx, arena);
  DepositBitField(element, offset,
                  ResizeToWidth(MemberBitsOf(rhs_val, field->type_kind, arena),
                                field->width, arena),
                  field->width);
  PerformBlockingAssign(select, element, ctx, arena);
  return true;
}

bool TrySelectBlockingAssign(const Expr* lhs, Logic4Vec& rhs_val,
                             SimContext& ctx, Arena& arena) {
  if (TryStructArrayMemberWrite(lhs, rhs_val, ctx, arena)) return true;
  // §8.11 with §23.9: in a method, `d[1] = v` writes the object's array
  // property ahead of a variable `d` of the module declaring the class.
  if (NamesOwnArrayProperty(lhs->base, ctx) &&
      TryWriteClassArrayElement(lhs, rhs_val, ctx, arena))
    return true;
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
  if (TryWriteStringElementChar(lhs, rhs_val, ctx, arena)) return true;
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

// §7.6/§7.10/§8.4: an assignment that rebuilds an array object, or
// constructs an object into an element, rather than writing a value: one
// array property to another (§7.6),
// `new` to an element of an array property of class handles or of a declared
// associative array of them (§7.8), or any assignment to a queue.
static bool TryArrayObjectAssign(const Stmt* stmt, SimContext& ctx,
                                 Arena& arena) {
  return TryClassArrayWholeAssign(stmt, ctx, arena) ||
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
// §7.5.1 and §8.4: `new[]` to a dynamic array property, and `new` to a class
// handle, a typed one or a member one, one arm of the dispatch below. The
// array form is asked first, since the property's element type may be a
// class, whose handle forms would construct one object for it.
static bool TryDispatchNewAssign(const Stmt* stmt, SimContext& ctx,
                                 Arena& arena) {
  return TryClassArrayNewAssign(stmt, ctx, arena) ||
         TryClassNewAssign(stmt, ctx, arena) ||
         TryTypedClassNewAssign(stmt, ctx, arena) ||
         TryMemberClassNewAssign(stmt, ctx, arena);
}

// §10.9 (printed page 261): the elements of the unpacked array the right-hand
// side of a deconstructing assignment names, left to right -- an array or a
// queue named whole, or the items of an assignment pattern, each evaluated
// before any member of the target is written -- else none.
static std::optional<std::vector<Logic4Vec>> DeconstructedElements(
    const Expr* rhs, SimContext& ctx, Arena& arena) {
  std::vector<Logic4Vec> elems;
  if (rhs->kind == ExprKind::kIdentifier) {
    if (const ArrayInfo* ai = ctx.FindArrayInfo(rhs->text);
        ai != nullptr && !ai->is_dynamic && !ai->is_queue) {
      CollectFixedArrayElements(rhs->text, *ai, ctx, elems);
    } else if (const QueueObject* q = ctx.FindQueue(rhs->text)) {
      elems = q->elements;
    } else {
      return std::nullopt;
    }
  } else {
    const Expr* pattern = UnwrapTypedPattern(rhs);
    if (pattern->kind != ExprKind::kAssignmentPattern ||
        !pattern->pattern_keys.empty() || pattern->repeat_count != nullptr)
      return std::nullopt;
    for (const Expr* item : pattern->elements)
      elems.push_back(EvalExpr(item, ctx, arena));
  }
  for (Logic4Vec& elem : elems) elem = OwnRhsWords(elem, arena);
  return elems;
}

// §10.9: an assignment pattern on the left of an assignment from an unpacked
// array deconstructs the array, each member taking one element, the first
// member the leftmost: `U'{a, b, c} = A` with `typedef byte U[3]` gives a, b
// and c A's three elements, and `U'{c, a, b} = '{a+1, b+1, c+1}` evaluates the
// three sums before c, a and b take them. Cut as a packed concatenation, the
// array's name read as one element and the last member alone received it.
static bool TryDeconstructingPatternAssign(const Stmt* stmt, SimContext& ctx,
                                           Arena& arena) {
  if (stmt->rhs == nullptr) return false;
  const Expr* target = UnwrapTypedPattern(stmt->lhs);
  if (target->kind != ExprKind::kAssignmentPattern ||
      !target->pattern_keys.empty())
    return false;
  auto elems = DeconstructedElements(stmt->rhs, ctx, arena);
  if (!elems || elems->size() != target->elements.size()) return false;
  for (size_t i = 0; i < elems->size(); ++i)
    PerformBlockingAssign(target->elements[i], (*elems)[i], ctx, arena);
  return true;
}

// §11.4.11 with Table 7-1: the element an unknown predicate yields from the two
// arms' elements `t` and `e` -- the value both hold where they match, and the
// element type's default, x for a four-state type and 0 for a two-state one,
// where they do not.
static Logic4Vec MergedConditionalElement(const Logic4Vec& t,
                                          const Logic4Vec& e,
                                          const ArrayInfo& dst, Arena& arena) {
  Logic4Vec a = ResizeToWidth(t, dst.elem_width, arena);
  Logic4Vec b = ResizeToWidth(e, dst.elem_width, arena);
  bool same = true;
  for (uint32_t w = 0; w < a.nwords && same; ++w)
    same = a.words[w].aval == b.words[w].aval &&
           a.words[w].bval == b.words[w].bval;
  if (same) return OwnRhsWords(a, arena);
  return dst.is_4state ? MakeAllX(arena, dst.elem_width)
                       : MakeLogic4VecVal(arena, dst.elem_width, 0);
}

// Whether the known predicate `cond` holds: any bit of it set.
static bool KnownPredicateHolds(const Logic4Vec& cond) {
  for (uint32_t w = 0; w < cond.nwords; ++w) {
    if (cond.words[w].aval != 0) return true;
  }
  return false;
}

// Writes each element of the array `dst_name` describes by `dst` the element
// MergedConditionalElement makes of the elements of the conditional `cond`'s
// two arms at the same position, left to right.
static void WriteMergedConditionalArray(std::string_view dst_name,
                                        const ArrayInfo& dst, const Expr* cond,
                                        SimContext& ctx, Arena& arena) {
  const Expr* t = cond->true_expr;
  const Expr* e = cond->false_expr;
  std::vector<Logic4Vec> tv;
  std::vector<Logic4Vec> ev;
  CollectFixedArrayElements(t->text, *ctx.FindArrayInfo(t->text), ctx, tv);
  CollectFixedArrayElements(e->text, *ctx.FindArrayInfo(e->text), ctx, ev);
  size_t count =
      std::min({static_cast<size_t>(dst.size), tv.size(), ev.size()});
  for (size_t i = 0; i < count; ++i) {
    auto offset = static_cast<uint32_t>(i);
    uint32_t idx =
        dst.is_descending ? dst.lo + dst.size - 1 - offset : dst.lo + offset;
    Variable* var = ctx.FindVariable(std::string(dst_name) + "[" +
                                     std::to_string(idx) + "]");
    if (var == nullptr) continue;
    var->value = MergedConditionalElement(tv[i], ev[i], dst, arena);
    var->NotifyWatchers();
  }
}

// §11.4.11: `r = c ? a : b` over fixed-size unpacked arrays. A known predicate
// copies the array it selects whole; an unknown one merges the two arms
// element by element (WriteMergedConditionalArray). Evaluated as a value, the
// conditional read each arm's name as one element, and nothing reached `r`.
static bool TryConditionalArrayAssign(const Stmt* stmt, SimContext& ctx,
                                      Arena& arena) {
  const Expr* rhs = stmt->rhs;
  if (rhs == nullptr || rhs->kind != ExprKind::kTernary ||
      stmt->lhs->kind != ExprKind::kIdentifier)
    return false;
  const ArrayInfo* dst = ctx.FindArrayInfo(stmt->lhs->text);
  const Expr* t = rhs->true_expr;
  const Expr* e = rhs->false_expr;
  if (dst == nullptr || dst->is_dynamic || dst->is_queue ||
      !dst->dim_sizes.empty() || t->kind != ExprKind::kIdentifier ||
      e->kind != ExprKind::kIdentifier || !ctx.FindArrayInfo(t->text) ||
      !ctx.FindArrayInfo(e->text))
    return false;
  Logic4Vec cond = EvalExpr(rhs->condition, ctx, arena);
  if (!cond.IsKnown()) {
    WriteMergedConditionalArray(stmt->lhs->text, *dst, rhs, ctx, arena);
    return true;
  }
  const Expr* src = KnownPredicateHolds(cond) ? t : e;
  CopyArrayElements(stmt->lhs->text, *dst, src->text,
                    *ctx.FindArrayInfo(src->text), ctx);
  return true;
}

bool TryDispatchSpecialBlockingAssign(const Stmt* stmt, SimContext& ctx,
                                      Arena& arena) {
  if (TryDeconstructingPatternAssign(stmt, ctx, arena)) return true;
  if (TryConditionalArrayAssign(stmt, ctx, arena)) return true;
  // §13.4.1 with §7.6 and §7.10: `av = fa()` copies the array the call
  // returned into the array or queue it is assigned to.
  if (TryCallResultArrayAssign(stmt, ctx, arena)) return true;
  if (TryDispatchSyncAssign(stmt, ctx, arena)) return true;
  if (TryDispatchNewAssign(stmt, ctx, arena)) return true;
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
  // §10.4.1: every writer below re-derives the target from the left-hand side's
  // index nodes, and the target's indices are evaluated once for all of them.
  LhsIndexPin pin(stmt->lhs, ctx, arena);
  // §10.9: a typed assignment pattern expression (type'{...}) is also a valid
  // left-hand target, and TryUnpackConcatLhs strips the type prefix so its
  // members unpack the RHS exactly as a bare positional pattern does.
  if (TryUnpackConcatLhs(stmt->lhs, rhs_val, ctx, arena)) return;
  if (stmt->lhs->kind == ExprKind::kStreamingConcat) {
    UnpackStreamingConcatLhs(stmt->lhs, rhs_val, ctx, arena);
    return;
  }
  rhs_val = ApplyStreamPackToTargetWidening(stmt, rhs_val, ctx, arena);
  if (TryContainerElementMemberWrite(stmt->lhs, rhs_val, ctx, arena)) return;
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
  // §10.4.1, as in ApplyGenericBlockingAssign: one evaluation of the target's
  // indices for every writer below.
  LhsIndexPin pin(lhs, ctx, arena);
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
