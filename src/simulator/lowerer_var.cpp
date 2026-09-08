#include <algorithm>
#include <string>
#include <string_view>
#include <vector>

#include "common/arena.h"
#include "common/diagnostic.h"
#include "elaborator/rtlir.h"
#include "elaborator/type_eval.h"
#include "parser/ast.h"
#include "simulator/class_object.h"
#include "simulator/eval_semaphore.h"
#include "simulator/eval_string.h"
#include "simulator/evaluation.h"
#include "simulator/lowerer.h"
#include "simulator/lowerer_register.h"
#include "simulator/queue_bound.h"
#include "simulator/sim_context.h"
#include "simulator/statement_assign.h"
#include "simulator/statement_assign_internal.h"

namespace delta {

// Builds the layout of a struct/union DataType: each field's bit offset (within
// its own width frame) and width, recursing into aggregate members so a nested
// member is reachable by its dotted path (§7.2.1). The result is arena-owned so
// the registered top-level copy's nested pointers stay valid.
static StructTypeInfo* BuildStructTypeInfo(const DataType* dtype,
                                           uint32_t total_width,
                                           std::string_view type_name,
                                           Arena& arena) {
  auto* info = arena.Create<StructTypeInfo>();
  info->type_name = type_name;
  info->is_packed = dtype->is_packed;
  info->is_union = (dtype->kind == DataTypeKind::kUnion);
  info->is_soft = dtype->is_soft;
  info->total_width = total_width;

  uint32_t offset = total_width;
  for (const auto& m : dtype->struct_members) {
    uint32_t fw = EvalStructMemberWidth(m);
    uint32_t field_off = 0;
    if (!info->is_union) {
      offset -= fw;
      field_off = offset;
    }
    StructFieldInfo fi{m.name, field_off, fw, m.type_kind};
    if (m.nested_type && !m.nested_type->struct_members.empty()) {
      fi.nested = BuildStructTypeInfo(m.nested_type, fw, m.type_name, arena);
    }
    info->fields.push_back(fi);
  }
  return info;
}

static void RegisterStructInfo(std::string_view name, const RtlirVariable& var,
                               SimContext& ctx, Arena& arena) {
  if (!var.dtype || var.dtype->struct_members.empty()) return;
  auto* info = BuildStructTypeInfo(var.dtype, var.width, name, arena);
  ctx.RegisterStructType(name, *info);
  ctx.SetVariableStructType(name, name);
}

static uint8_t StringLiteralByteAt(const Logic4Vec& packed, uint32_t i) {
  uint32_t nbytes = packed.width / 8;
  if (i >= nbytes) return 0;
  uint32_t byte_idx = nbytes - 1 - i;
  uint32_t word = (byte_idx * 8) / 64;
  uint32_t bit = (byte_idx * 8) % 64;
  if (word >= packed.nwords) return 0;
  return static_cast<uint8_t>((packed.words[word].aval >> bit) & 0xFF);
}

// §6.8, Table 6-7: the value an element left without one takes -- the default
// initial value of its own type, 'x for a 4-state integral and '0 for a 2-state
// one. An element is a variable of the array's element type, so the rule
// reaches it exactly as it reaches a scalar declared alongside; only the
// 2-state case is zero. Both of this function's callers write the same rule,
// and the two makers of array leaves have already drifted once over a
// per-element property of exactly this kind (the is_4state/is_signed flags), so
// it is written once.
static Logic4Vec Table67ElementDefault(const RtlirVariable& var, Arena& arena) {
  return var.is_4state ? MakeAllX(arena, var.width)
                       : MakeLogic4VecVal(arena, var.width, 0);
}

// §10.5 makes a variable declaration assignment "a special case of procedural
// assignment", and §10.9.1 evaluates each pattern item in the assignment
// context of its element, so an item stored on a leaf takes the two steps a
// runtime write to that element takes: §10.7's resize to the element width, and
// §6.11.2's conversion of every unknown or high-impedance bit to zero on the
// way into a 2-state type. The resize is not the second of those: ResizeToWidth
// answers its argument untouched when the widths already match, and copies the
// bval plane word for word when they differ, so an x reached a `bit` element
// either way -- where the same value written to the same element by a statement
// (WriteVar), or to a scalar of the same type by a declaration
// (CoerceVarInitValue), reads 0. The three helpers below each stored their item
// without it.
//
// The copy is taken before the coercion because the coercion writes in place
// and an item that is a bare name is answered with that variable's own
// Logic4Vec (§6.8): coercing through it would clear the source's own unknown
// bits, which is the defect #3563 removed elsewhere. It is worth taking on the
// 4-state path too, a leaf sharing one buffer with the variable its initializer
// read being the same family again.
static Logic4Vec CoerceArrayInitItem(const RtlirVariable& var, Logic4Vec val,
                                     Arena& arena) {
  val = OwnRhsWords(ResizeToWidth(val, var.width, arena), arena);
  if (!var.is_4state && !var.is_string && !var.is_real) CoerceTo2State(val);
  return val;
}

static void InitArrayElement(const RtlirVariable& var, uint32_t elem_idx,
                             Variable* elem, SimContext& ctx, Arena& arena) {
  if (!var.init_expr) {
    elem->value = Table67ElementDefault(var, arena);
    return;
  }

  if (var.init_expr->kind == ExprKind::kStringLiteral) {
    auto packed = EvalExpr(var.init_expr, ctx, arena);
    auto b = StringLiteralByteAt(packed, elem_idx);
    elem->value = MakeLogic4VecVal(arena, var.width, b);
    return;
  }
  auto& elements = var.init_expr->elements;
  if (elem_idx < elements.size()) {
    elem->value = CoerceArrayInitItem(
        var, EvalExpr(elements[elem_idx], ctx, arena), arena);
    return;
  }
  // Past the end of the pattern's items no value was supplied for this element
  // either, so Table 6-7 governs it the same way.
  elem->value = Table67ElementDefault(var, arena);
}

static void InitArrayFromReplicate(const RtlirVariable& var, uint32_t elem_idx,
                                   Variable* elem, SimContext& ctx,
                                   Arena& arena) {
  auto* rep = var.init_expr->elements[0];
  auto inner_count = static_cast<uint32_t>(rep->elements.size());
  if (inner_count == 0) {
    elem->value = MakeLogic4VecVal(arena, var.width, 0);
    return;
  }
  elem->value = CoerceArrayInitItem(
      var, EvalExpr(rep->elements[elem_idx % inner_count], ctx, arena), arena);
}

// §10.9.1: "An index:value specifies an explicit value for a keyed element
// index." The clause makes it "an error to specify the same index more than
// once in a single array pattern expression", so the first key that names this
// element is the only one that can. Null when no index key names it.
static const Expr* FindIndexKeyedItem(const Expr* pat, uint32_t idx,
                                      SimContext& ctx, Arena& arena) {
  for (size_t i = 0; i < pat->pattern_keys.size(); ++i) {
    if (i >= pat->elements.size()) break;
    const auto* key = pat->pattern_keys[i];
    if (key->text == "default" || IsTypeKeyword(key->text)) continue;
    if (PatternKeyIndex(key, ctx, arena) == idx) return pat->elements[i];
  }
  return nullptr;
}

// §10.9.1: "For type:value, if the element or subarray type of the array
// matches this type, then each element or subarray that has not already been
// set by an index key above shall be set to the value." Null when no type key
// matches this kind.
static const Expr* FindTypeKeyedItem(const Expr* pat, DataTypeKind kind) {
  for (size_t i = 0; i < pat->pattern_keys.size(); ++i) {
    if (i >= pat->elements.size()) break;
    auto key = pat->pattern_keys[i]->text;
    if (IsTypeKeyword(key) && TypeKeyMatchesKind(key, kind))
      return pat->elements[i];
  }
  return nullptr;
}

// §10.9.1: "The default:value applies to elements or subarrays that are not
// matched by either index or type key." Null when the pattern writes no
// default key.
static const Expr* FindDefaultKeyedItem(const Expr* pat) {
  for (size_t i = 0; i < pat->pattern_keys.size(); ++i) {
    if (i >= pat->elements.size()) break;
    if (pat->pattern_keys[i]->text == "default") return pat->elements[i];
  }
  return nullptr;
}

// §10.9.1's three matching rules, asked in the order the clause writes them:
// index key, then type key, then default. Null when none of them covers this
// element -- which the clause forbids ("Every element shall be covered by one
// of these rules"), so it is a malformed pattern rather than a defined value.
static const Expr* FindKeyedItem(const Expr* pat, uint32_t idx,
                                 DataTypeKind kind, SimContext& ctx,
                                 Arena& arena) {
  if (const Expr* item = FindIndexKeyedItem(pat, idx, ctx, arena)) return item;
  if (const Expr* item = FindTypeKeyedItem(pat, kind)) return item;
  return FindDefaultKeyedItem(pat);
}

static void InitArrayFromNamed(const RtlirVariable& var, uint32_t idx,
                               Variable* elem, SimContext& ctx, Arena& arena) {
  // §10.9.1: a key resolves a value that is then evaluated in the assignment
  // context of the element. An element covered by none of the keys is a pattern
  // the clause forbids -- "Every element shall be covered by one of these
  // rules" -- and is reported at elaboration; the branch stays reachable for a
  // caller that does not stop on that report, and answers Table 6-7 as the
  // positional maker above and the multidimensional one below do rather than
  // the known zero it gave, which had one spelling of an illegal pattern
  // reading 00 where the other read 'x.
  const Expr* item =
      FindKeyedItem(var.init_expr, idx, var.elem_type_kind, ctx, arena);
  elem->value =
      item ? CoerceArrayInitItem(var, EvalExpr(item, ctx, arena), arena)
           : Table67ElementDefault(var, arena);
}

namespace {
// §7.4.2: bundle for materializing the leaves of a fixed multidimensional
// unpacked array, keeping the recursive walk within the parameter-count limit.
struct MultiDimArray {
  const RtlirVariable& var;
  SimContext& ctx;
  Arena& arena;
};
}  // namespace

// §10.9.1: "A syntax resembling replications ... can be used in array
// assignment patterns as well. Each replication shall represent an entire
// single dimension." A replicated item is therefore not one element's value but
// the body of the dimension it stands for, cycled across that dimension's
// positions -- which is what makes the clause's own `'{2{'{3{y}}}}` the same as
// `'{'{y,y,y},'{y,y,y}}`. Null when this pattern is not the replicated form.
static const std::vector<Expr*>* ReplicateBody(const Expr* pat) {
  if (!pat->pattern_keys.empty()) return nullptr;
  if (pat->elements.size() != 1) return nullptr;
  if (pat->elements[0]->kind != ExprKind::kReplicate) return nullptr;
  const auto& body = pat->elements[0]->elements;
  return body.empty() ? nullptr : &body;
}

// §10.9.1: "the braces shall match the array dimensions", so an item that is
// itself a brace pattern is the sub-pattern of the next dimension in. Anything
// else is a value, which is what a type or default key resolves to for a whole
// subarray -- the clause applies those "recursively ... to each of its elements
// or subarrays", so such a value reaches every leaf beneath it.
static bool IsDimPattern(const Expr* item) {
  return item->kind == ExprKind::kAssignmentPattern ||
         item->kind == ExprKind::kConcatenation;
}

// §10.9: only a brace pattern matches the array's dimensions, so only one is
// distributed into the leaves; a typed assignment pattern expression
// (`T'{...}`) parses as a cast wrapping one, so unwrap that first. Null for a
// declaration with no initializer, or one whose initializer is not a pattern at
// all.
static const Expr* ArrayInitPattern(const Expr* init) {
  if (!init) return nullptr;
  if (init->kind == ExprKind::kCast && init->lhs && IsDimPattern(init->lhs))
    return init->lhs;
  return IsDimPattern(init) ? init : nullptr;
}

// §10.9.1: the item of `pat` that fills one dimension's element at address
// `idx`, position `pos` within that dimension. All three item forms the clause
// admits are read here -- keyed, replicated, and positional -- so the descent
// below meets the same three the single-dimension maker does. Null when the
// pattern supplies nothing for this element.
static const Expr* SelectDimItem(const Expr* pat, uint32_t idx, uint32_t pos,
                                 const MultiDimArray& m) {
  if (!pat->pattern_keys.empty())
    return FindKeyedItem(pat, idx, m.var.elem_type_kind, m.ctx, m.arena);
  if (const auto* body = ReplicateBody(pat)) return (*body)[pos % body->size()];
  return pos < pat->elements.size() ? pat->elements[pos] : nullptr;
}

// Materializes one leaf variable of the array and gives it the value of the
// pattern item that reached it, or §6.8 Table 6-7's default when none did.
static void CreateMultiDimLeaf(const MultiDimArray& m, const std::string& name,
                               const Expr* item) {
  auto* stored = m.arena.Create<std::string>(name);
  auto* elem = m.ctx.CreateVariable(*stored, m.var.width);
  RecordPackedRange(m.var.dtype, elem, m.ctx, m.arena);
  elem->is_4state = m.var.is_4state;
  elem->is_signed = m.var.is_signed;
  if (!item) {
    // §6.8, Table 6-7: nothing covered this leaf, so it keeps the default
    // initial value of its type -- the 'x CreateVariable seeded for a 4-state
    // element (masked to the width there, which MakeAllX does not do), and '0
    // for a 2-state one. Exactly what an uncovered leaf held before this walk
    // carried an initializer at all.
    if (!m.var.is_4state)
      elem->value = MakeLogic4VecVal(m.arena, m.var.width, 0);
    return;
  }
  // §10.9.1: "Each expression item shall be evaluated in the context of an
  // assignment to the type of the corresponding element in the array", so the
  // item is coerced to the element width (a no-op when they already match).
  // §6.8 then makes the leaf "an abstraction of a data storage element" that
  // stores a value of its own, so it takes its own words: a bare item name of
  // the leaf's width is answered with that variable's Logic4Vec, ResizeToWidth
  // hands it straight back, and without the copy every leaf of
  // `'{2{'{3{y}}}}` would share y's storage.
  elem->value = OwnRhsWords(
      ResizeToWidth(EvalExpr(item, m.ctx, m.arena), m.var.width, m.arena),
      m.arena);
}

// §7.4.2: recursively create one leaf variable per element of a fixed
// multidimensional unpacked array, named arr[i0][i1]... in row-major order so a
// compound select (eval_select.cpp) and a nested assignment pattern resolve to
// it. `item` is the part of the declaration initializer that reached this
// subtree: §10.9.1 has "the braces shall match the array dimensions", so the
// initializer is a tree of the array's own shape and the walk carries the
// sub-pattern for the current dimension down beside the prefix it already
// carried. This is the step the two makers of array leaves differed by -- the
// single-dimension one applied the initializer and this one never read it, so
// the clause's own `int n[1:2][1:3] = '{2{'{3{y}}}};` read 0 at all six leaves.
// A leaf no item reaches keeps §6.8 Table 6-7's default, unchanged.
static void CreateMultiDimLeaves(const MultiDimArray& m,
                                 const std::string& prefix, size_t d,
                                 const Expr* item) {
  const auto& sizes = m.var.unpacked_dim_sizes;
  if (d == sizes.size()) {
    CreateMultiDimLeaf(m, prefix, item);
    return;
  }
  const auto& dim = m.var.unpacked_dims[d];
  // §11.5.2 counts an address from the smaller of the two bounds the
  // declaration wrote, whichever way round it wrote them, while §10.9.1 counts
  // a pattern's positional items from the dimension's left bound. A descending
  // dimension therefore takes them the other way round, exactly as the
  // single-dimension maker's pat_idx does; is_descending on the variable
  // describes only the first dimension, so each dimension is asked its own
  // bounds instead.
  bool descending = dim.left > dim.right;
  const Expr* pat = (item != nullptr && IsDimPattern(item)) ? item : nullptr;
  for (uint32_t i = 0; i < sizes[d]; ++i) {
    int64_t idx = dim.Low() + i;
    // A value standing where this dimension's braces were expected is a whole
    // subarray's value, so it passes down unchanged to every leaf beneath.
    const Expr* sub =
        pat ? SelectDimItem(pat, static_cast<uint32_t>(idx),
                            descending ? (sizes[d] - 1 - i) : i, m)
            : item;
    CreateMultiDimLeaves(m, prefix + "[" + std::to_string(idx) + "]", d + 1,
                         sub);
  }
}

// §7.4.2: register a fixed multidimensional unpacked array and create its
// leaves. The single-dimension lo/size keep describing the outermost dimension
// (so existing whole-array and outer-index paths still work), while dim_los /
// dim_sizes carry every dimension. Returns false for a single-dimension array.
static bool TryCreateMultiDimArray(std::string_view name,
                                   const RtlirVariable& var, SimContext& ctx,
                                   Arena& arena) {
  if (var.unpacked_dim_sizes.size() < 2) return false;
  if (var.unpacked_dims.size() != var.unpacked_dim_sizes.size()) return false;
  ArrayInfo info;
  info.lo = static_cast<uint32_t>(var.unpacked_lo);
  info.size = var.unpacked_size;
  info.elem_width = var.width;
  info.is_descending = var.is_descending;
  info.is_4state = var.is_4state;
  info.elem_type_kind = var.elem_type_kind;
  // ArrayInfo::dim_los is uint32_t, so a negative bound does not survive the
  // copy. §7.4.2 admits one; carrying it into the simulator is separate work.
  // The direction beside it does survive: it is the comparison of the two
  // int64_t bounds, made here before either is narrowed, so `[-1:-3]` records
  // as descending however its low bound lands.
  info.dim_los.reserve(var.unpacked_dims.size());
  info.dim_descending.reserve(var.unpacked_dims.size());
  for (const auto& dim : var.unpacked_dims) {
    info.dim_los.push_back(static_cast<uint32_t>(dim.Low()));
    info.dim_descending.push_back(dim.left > dim.right);
  }
  info.dim_sizes = var.unpacked_dim_sizes;
  ctx.RegisterArray(name, info);
  CreateMultiDimLeaves(MultiDimArray{var, ctx, arena}, std::string(name), 0,
                       ArrayInitPattern(var.init_expr));
  return true;
}

static void CreateArrayElements(std::string_view name, const RtlirVariable& var,
                                SimContext& ctx, Arena& arena) {
  if (var.unpacked_size == 0) return;
  if (TryCreateMultiDimArray(name, var, ctx, arena)) return;
  ArrayInfo info;
  info.lo = static_cast<uint32_t>(var.unpacked_lo);
  info.size = var.unpacked_size;
  info.elem_width = var.width;
  info.is_descending = var.is_descending;
  info.is_4state = var.is_4state;
  info.elem_type_kind = var.elem_type_kind;
  ctx.RegisterArray(name, info);

  bool named = var.init_expr && !var.init_expr->pattern_keys.empty();
  bool replicate = var.init_expr && var.init_expr->elements.size() == 1 &&
                   var.init_expr->elements[0]->kind == ExprKind::kReplicate;
  for (uint32_t i = 0; i < var.unpacked_size; ++i) {
    uint32_t idx = static_cast<uint32_t>(var.unpacked_lo) + i;
    auto elem_name = std::string(name) + "[" + std::to_string(idx) + "]";
    auto* stored = arena.Create<std::string>(std::move(elem_name));
    auto* elem = ctx.CreateVariable(*stored, var.width);
    RecordPackedRange(var.dtype, elem, ctx, arena);
    // §6.11.2: in a 2-state type "any unknown or high-impedance bits shall be
    // converted to zeros", and the flag is what decides whether that
    // conversion runs at all -- WriteVar coerces only when it is clear, so an
    // element left at Variable's 4-state default keeps an x a runtime write
    // put there. The two makers of array leaves disagreed about this:
    // CreateMultiDimLeaves carried the declaration's state-ness and
    // signedness onto every leaf and this one carried neither, so
    // `bit [7:0] c [0:1]` and `bit [7:0] d [0:1][0:1]` answered `= 8'hxx`
    // differently on one write path. The sibling was right; an element is a
    // variable of the array's element type, so it is 2-state exactly when the
    // declaration is. §6.11.3 likewise fixes signedness by the declaration
    // rather than by whatever value flowed in.
    elem->is_4state = var.is_4state;
    elem->is_signed = var.is_signed;
    uint32_t pat_idx = var.is_descending ? (var.unpacked_size - 1 - i) : i;
    if (named) {
      InitArrayFromNamed(var, idx, elem, ctx, arena);
    } else if (replicate) {
      InitArrayFromReplicate(var, pat_idx, elem, ctx, arena);
    } else {
      InitArrayElement(var, pat_idx, elem, ctx, arena);
    }
  }
}

static std::string StripQuotes(std::string_view s) {
  if (s.size() >= 2 && s.front() == '"' && s.back() == '"')
    return std::string(s.substr(1, s.size() - 2));
  return std::string(s);
}

// §7.5.1: a dynamic array declaration may use the new[] constructor as its
// declaration-assignment right-hand side. Size the array, default-initialize
// its elements, then copy from the optional initialization array. Returns true
// when the init_expr was a new[] constructor (handled here).
static bool LowerDynArrayNewInit(const Expr* init_expr, QueueObject* q,
                                 SimContext& ctx, Arena& arena) {
  if (init_expr->kind != ExprKind::kCall || init_expr->text != "new" ||
      init_expr->args.empty())
    return false;

  auto sz_val = EvalExpr(init_expr->args[0], ctx, arena);
  int64_t sz = SignExtend(sz_val.ToUint64(), sz_val.width);
  if (sz < 0) {
    ctx.GetDiag().Error(init_expr->args[0]->range.start,
                        "dynamic array new[] size is negative",
                        Subclause("7.5.1"));
    return true;
  }
  // §7.5.1: with no initialization expression "the elements are initialized to
  // the default value for their type" -- elements, each one initialized, and
  // §6.8 makes each "an abstraction of a data storage element" that "shall
  // store a value from one assignment to the next", so each owes its own
  // words. vector::assign(n, value) copy-constructs every slot it makes from
  // the single value it is handed, and a Logic4Vec copy carries the `words`
  // pointer rather than the words, so filling that way gave `int d[] =
  // new[4];` one buffer read four times. Building the elements one at a time
  // gives each its own allocation.
  q->elements.clear();
  q->elements.reserve(static_cast<size_t>(sz));
  for (int64_t i = 0; i < sz; ++i)
    q->elements.push_back(MakeLogic4VecVal(arena, q->elem_width, 0));
  if (init_expr->args.size() >= 2) {
    auto* src_expr = init_expr->args[1];
    if (src_expr && src_expr->kind == ExprKind::kIdentifier) {
      if (auto* src = ctx.FindQueue(src_expr->text)) {
        // §7.5.1: "The optional initialization expression is used to
        // initialize the dynamic array." Each entry it initializes is a store
        // of its own, so each takes a copy of the source entry's words rather
        // than the pointer a plain Logic4Vec assignment would leave the two
        // sharing. The clause says what the sharing breaks: reinitializing
        // with new "is destructive ... and all preexisting references to array
        // elements become outdated", and an entry still naming the source's
        // words is exactly such a reference left live.
        size_t copy_len = std::min(q->elements.size(), src->elements.size());
        for (size_t i = 0; i < copy_len; ++i)
          q->elements[i] = OwnRhsWords(src->elements[i], arena);
      }
    }
  }
  EnforceQueueBound(q, "new[]", init_expr->range.start, ctx);
  q->AssignFreshIds();
  return true;
}

// `q` is the store this declaration's own name was just created under, passed
// rather than looked up again: the name is already qualified by the instance,
// and SimContext::FindQueue resolves a name within the instance being built,
// so a second lookup would search for the qualified name inside the instance
// that qualified it.
void Lowerer::LowerDynArrayInit(QueueObject* q, const RtlirVariable& var) {
  if (!q || !var.init_expr) return;

  if (LowerDynArrayNewInit(var.init_expr, q, ctx_, arena_)) return;

  if (var.init_expr->kind != ExprKind::kAssignmentPattern &&
      var.init_expr->kind != ExprKind::kConcatenation)
    return;
  for (auto* elem : var.init_expr->elements) {
    q->elements.push_back(EvalExpr(elem, ctx_, arena_));
  }
  EnforceQueueBound(q, "declaration initializer", var.init_expr->range.start,
                    ctx_);
  // Every element carries an id, and the two lists are indexed together, so
  // they have to be the same length however the elements arrived. Leaving the
  // ids empty here made an initialized queue's first insert at a nonzero index
  // offset past the end of the id list.
  q->AssignFreshIds();
}

void Lowerer::InitAssocDefault(const Expr* init, AssocArrayObject* aa) {
  if (!init || init->kind != ExprKind::kAssignmentPattern) return;
  for (size_t i = 0; i < init->pattern_keys.size(); ++i) {
    if (i >= init->elements.size()) break;
    const auto* key = init->pattern_keys[i];
    // §7.9.11's literal gives the array a default and its named entries their
    // values, and each of those is storage of its own under §6.8. A bare item
    // name of the element width is answered with that variable's own
    // Logic4Vec, so without the copy `int aa[int] = '{default: seed}` would
    // leave the array's default sharing seed's words: a later in-place deposit
    // into seed -- a bit-select write, say -- would rewrite the default, and
    // through it every entry allocated from the default.
    auto val = OwnRhsWords(EvalExpr(init->elements[i], ctx_, arena_), arena_);
    if (key->text == "default") {
      aa->has_default = true;
      aa->default_value = val;
    } else if (aa->is_string_key) {
      aa->str_data[StripQuotes(key->text)] = val;
    } else {
      // §7.9.11: an integer-keyed entry is written at the index its key
      // evaluates to, which is the whole key expression's value. It is read as
      // an index of this array's declared index type, the same way a key
      // written on the left of an assignment to one element is, so that a key
      // and an index that name one entry land on one entry.
      auto key_val = EvalExpr(key, ctx_, arena_);
      aa->int_data[AssocIntKey(key_val, aa->is_wildcard, aa->index_width,
                               aa->is_index_signed)] = val;
    }
  }
}

static void ApplyStructMemberDefaults(std::string_view name,
                                      const RtlirVariable& var, Variable* v,
                                      SimContext& ctx, Arena& arena) {
  if (!var.dtype || var.dtype->struct_members.empty()) return;
  if (var.dtype->kind == DataTypeKind::kUnion) return;
  auto* sinfo = ctx.GetVariableStructType(name);
  if (!sinfo) return;
  for (const auto& f : sinfo->fields) {
    for (const auto& m : var.dtype->struct_members) {
      if (m.name != f.name || !m.init_expr) continue;
      // Multi-word safe: a field at bit offset >= 64 cannot be reached through
      // ToUint64() (which keeps only the low 64 bits).
      Logic4Vec val = EvalExpr(m.init_expr, ctx, arena);
      DepositBitField(v->value, f.bit_offset, val, f.width);
      break;
    }
  }
}

// §7.8.7: an element allocated by a write starts at the initial value its
// type gives it, which for a struct is its members' initializers rather than
// zero. LowerVar has already deposited those onto the variable it created
// under this name, which models one element of the array, so the pattern is
// read back from there rather than evaluated a second time.
static void RecordAssocElemInit(std::string_view name, const RtlirVariable& var,
                                AssocArrayObject* aa, SimContext& ctx,
                                Arena& arena) {
  if (!var.dtype || var.dtype->struct_members.empty()) return;
  if (var.dtype->kind == DataTypeKind::kUnion) return;
  bool any_init = false;
  for (const auto& m : var.dtype->struct_members) {
    if (m.init_expr) any_init = true;
  }
  if (!any_init) return;
  auto* elem = ctx.FindVariable(name);
  if (!elem) return;
  aa->has_elem_init = true;
  // The element model is a live Variable, so the initial value the array keeps
  // takes its own words rather than the variable's: an entry allocated from
  // elem_init is §6.8 storage of its own (see AssocAllocValue), and a stored
  // initial value that shares with a variable would be one more name for the
  // same buffer behind them all.
  aa->elem_init = OwnRhsWords(elem->value, arena);
}

void Lowerer::LowerVarAggregate(std::string_view name,
                                const RtlirVariable& var) {
  if (var.is_queue) {
    auto* q =
        ctx_.CreateQueue(name, var.width, var.queue_max_size, var.is_4state);
    // §7.10.1: a queue may be initialized from an assignment-pattern literal
    // (e.g. int q[$] = '{10, 20, 30}). Populate its elements like a dynamic
    // array; LowerDynArrayInit is a no-op when there is no initializer.
    LowerDynArrayInit(q, var);
  } else if (var.is_dynamic) {
    // Carry the element's state-ness onto the backing store: §21.4.2 keys the
    // x/z-to-0 memory-load coercion on it, and it governs 2-state defaults.
    auto* q = ctx_.CreateQueue(name, var.width, /*max_size=*/-1, var.is_4state);
    LowerDynArrayInit(q, var);

    ArrayInfo info;
    info.is_dynamic = true;
    info.elem_width = var.width;
    info.is_4state = var.is_4state;
    ctx_.RegisterArray(name, info);
  } else if (var.is_assoc) {
    auto* aa = ctx_.CreateAssocArray(
        name, var.width, var.is_string_index,
        AssocArraySpec{var.assoc_index_width, var.is_wildcard_index,
                       var.is_4state, var.is_index_signed});
    InitAssocDefault(var.init_expr, aa);
    RecordAssocElemInit(name, var, aa, ctx_, arena_);
  } else {
    CreateArrayElements(name, var, ctx_, arena_);
  }
}

// §21.7.5 (Table 21-11): the effective type keyword under which a variable is
// dumped to a VCD file. Normally the declared element type keyword, with two
// substitutions the table calls out: a typed enum is dumped as its specified
// base type rather than the default integer/32, and a packed structure is
// dumped as a single reg vector (masqueraded here as a bit vector so it carries
// the reg keyword and its collapsed total width, exactly like a packed array).
static DataTypeKind VcdEffectiveDeclKind(const RtlirVariable& var) {
  DataTypeKind kind = var.elem_type_kind;
  // A variable declared through a typedef carries the named kind; the
  // elaborator resolved the underlying type onto var.dtype, so recover its kind
  // to see the real enum/struct/integral type the typedef names.
  if (kind == DataTypeKind::kNamed && var.dtype != nullptr)
    kind = var.dtype->kind;
  if (kind == DataTypeKind::kEnum && var.dtype != nullptr &&
      var.dtype->enum_base_kind != DataTypeKind::kImplicit)
    return var.dtype->enum_base_kind;
  if (kind == DataTypeKind::kStruct && var.dtype != nullptr &&
      var.dtype->is_packed)
    return DataTypeKind::kBit;
  return kind;
}

// §15.3: a semaphore is a bucket of keys, and the declaration is what brings
// the bucket into being. §15.3.1's new() sets how many keys are in it and
// defaults that to none, so a bucket no new() has reached yet is empty and
// every get() on it waits. Does nothing for a variable of any other type.
static void CreateSemaphoreForVar(std::string_view name,
                                  const RtlirVariable& var, SimContext& ctx,
                                  Arena& arena) {
  if (var.class_type_name != "semaphore") return;
  auto* sem = ctx.CreateSemaphore(name, 0);
  if (var.init_expr && var.init_expr->kind == ExprKind::kCall &&
      var.init_expr->text == "new") {
    sem->key_count = SemaphoreKeyArg(var.init_expr, ctx, arena, 0);
  }
}

void Lowerer::LowerVar(std::string_view name, const RtlirVariable& var) {
  uint32_t width = var.class_type_name.empty() ? var.width : 64;
  auto* v = ctx_.CreateVariable(name, width);
  RecordPackedRange(var.dtype, v, ctx_, arena_);

  // §25.9: track virtual interface variables so assignments bind them to an
  // interface instance and component access redirects through that binding.
  if (var.elem_type_kind == DataTypeKind::kVirtualInterface) {
    ctx_.RegisterVirtualInterfaceVar(v);
  }

  if (!var.is_4state && !var.is_event && !var.is_string && !var.is_chandle) {
    v->value = MakeLogic4VecVal(arena_, width, 0);
  }

  if (var.is_chandle) v->value = MakeLogic4VecVal(arena_, width, 0);
  v->is_4state = var.is_4state;
  if (var.is_event) v->is_event = true;
  if (var.is_signed) v->is_signed = true;
  if (var.is_string) ctx_.RegisterStringVariable(name);
  if (var.is_real) ctx_.RegisterRealVariable(name);
  // §21.7.5 (Table 21-11): remember the declared type keyword so this
  // variable's $var declaration masquerades as the matching 1364-2005 var_type
  // when dumped.
  ctx_.Vcd().SetVcdVarKind(name, VcdEffectiveDeclKind(var));
  // §21.2.1.6: the %p renderer prints a null chandle as "null", so it needs to
  // know which variables are chandles.
  if (var.is_chandle) ctx_.RegisterChandleVariable(name);
  RegisterStructInfo(name, var, ctx_, arena_);
  if (var.init_expr) {
    LowerVarInit(name, var, v, width);
  }
  if (!var.init_expr) ApplyStructMemberDefaults(name, var, v, ctx_, arena_);
  if (!var.class_type_name.empty())
    ctx_.SetVariableClassType(name, var.class_type_name);
  CreateSemaphoreForVar(name, var, ctx_, arena_);

  if (!var.enum_type_name.empty() && var.dtype) {
    RegisterEnumForCast(name, var);
  }
  LowerVarAggregate(name, var);
}

// §8.7/§6.8: a class-handle declaration initialized with `new` constructs the
// object as part of static initialization (before any initial/always block),
// the same as a runtime `handle = new(args)` assignment. Generic EvalExpr
// cannot do this because a bare `new` call carries no target class type; the
// declared handle type supplies it. Returns true when it handled a class-new
// initializer.
static bool TryLowerClassNewVarInit(const RtlirVariable& var, Variable* v,
                                    SimContext& ctx, Arena& arena) {
  if (var.class_type_name.empty() || var.init_expr->kind != ExprKind::kCall ||
      var.init_expr->text != "new")
    return false;
  v->value = EvalClassNew(var.class_type_name, var.init_expr, ctx, arena,
                          var.init_expr->range.start);
  return true;
}

// §6.17/§15: an event variable initialized to `null` is a null event; one
// initialized to another event identifier aliases that event. Returns true when
// it handled an event initializer.
static bool TryLowerEventVarInit(std::string_view name,
                                 const RtlirVariable& var, Variable* v,
                                 SimContext& ctx) {
  if (!var.is_event || var.init_expr->kind != ExprKind::kIdentifier)
    return false;
  if (var.init_expr->text == "null") {
    v->is_null_event = true;
    return true;
  }
  auto* target = ctx.FindVariable(var.init_expr->text);
  if (target && target->is_event) {
    ctx.AliasVariable(name, var.init_expr->text);
    return true;
  }
  return false;
}

// §6.12.1: a declaration initializer is an assignment, so an initializer that
// crosses the real/integer boundary undergoes the same implicit conversion as a
// procedural assign (round-to-nearest ties-away one way; x/z->0 numeric
// conversion the other), never a raw bit reinterpretation of the operand.
// §6.11.2: assigning a 4-state initializer to a 2-state variable is likewise an
// automatic conversion, so unknown/high-impedance bits become zero -- the
// width-mismatch projection already drops them, and this covers the
// matching-width case too.
Logic4Vec Lowerer::CoerceVarInitValue(const RtlirVariable& var, Logic4Vec val,
                                      uint32_t width) {
  if (val.is_real != var.is_real && !var.is_string && !val.is_string &&
      !var.is_event && !var.is_chandle)
    val = ConvertRealForKnownLhs(val, var.is_real, width, arena_);
  if (val.width != width && !var.is_real && !var.is_string)
    val = MakeLogic4VecVal(arena_, width, val.ToUint64());
  if (var.is_string) val = StripStringZeros(val, arena_);
  if (!var.is_4state && !var.is_string && !var.is_real && !var.is_event &&
      !var.is_chandle)
    CoerceTo2State(val);
  return val;
}

// §11.6: a declaration initializer is an assignment, so its target width is the
// context the initializer expression is evaluated in, exactly as for a
// procedural assign. For a plain integral scalar target this lets an arithmetic
// initializer such as `logic [16:0] s = a + b;` keep the carry-out that a
// self-determined evaluation at the operands' own width would drop. Aggregate,
// real, string, event, and chandle initializers keep their dedicated sizing and
// stay self-determined.
void Lowerer::LowerVarInit(std::string_view name, const RtlirVariable& var,
                           Variable* v, uint32_t width) {
  if (TryLowerEventVarInit(name, var, v, ctx_)) return;
  if (TryLowerClassNewVarInit(var, v, ctx_, arena_)) return;
  // §8.8: `C c = D::new;` at module scope constructs the specified type during
  // static initialization. The argument-less typed constructor is a bare
  // scope-resolved member access, not a `new` call, so route it to the typed
  // construction path before the generic initializer lowering below.
  {
    Logic4Vec typed;
    if (var.init_expr &&
        TryEvalTypedConstructorNew(var.init_expr, ctx_, arena_, typed)) {
      v->value = typed;
      return;
    }
  }

  auto* sinfo = ctx_.GetVariableStructType(name);

  auto* init = var.init_expr;
  if (init->kind == ExprKind::kCast && init->lhs &&
      init->lhs->kind == ExprKind::kAssignmentPattern)
    init = init->lhs;
  // §10.9.2: a struct-typed declaration initializer that is an assignment
  // pattern (keyed or positional) is evaluated against the member layout, so
  // each member expression is coerced to its member's type.
  if (init->kind == ExprKind::kAssignmentPattern && sinfo) {
    v->value = EvalStructPatternValue(init, sinfo, ctx_, arena_);
    return;
  }
  bool self_determined = sinfo != nullptr || var.is_real || var.is_string ||
                         var.is_event || var.is_chandle ||
                         init->kind == ExprKind::kAssignmentPattern;
  auto val = EvalExpr(var.init_expr, ctx_, arena_, self_determined ? 0 : width);
  v->value = CoerceVarInitValue(var, val, width);

  // §11.9: initializing a tagged-union variable with a tagged expression
  // establishes the variable's active tag, exactly as the procedural
  // `u = tagged Member value` assignment does. Without this the tag would stay
  // undefined and a later member access would not be checked against the tag
  // set by the initializer.
  if (var.init_expr->kind == ExprKind::kTagged && var.init_expr->rhs)
    ctx_.SetVariableTag(name, var.init_expr->rhs->text);
}

void Lowerer::RegisterEnumForCast(std::string_view name,
                                  const RtlirVariable& var) {
  ctx_.SetVariableEnumType(name, var.enum_type_name);
}

void Lowerer::RegisterEnumTypes(const RtlirModule* mod) {
  for (const auto& [name, members] : mod->enum_types) {
    if (ctx_.FindEnumType(name)) continue;
    EnumTypeInfo info;
    info.type_name = name;
    for (const auto& m : members) {
      info.members.push_back({m.name, static_cast<uint64_t>(m.value)});
    }
    ctx_.RegisterEnumType(name, info);
  }
}

}  // namespace delta
