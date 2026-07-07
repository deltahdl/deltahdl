#include "simulator/statement_assign.h"

#include <algorithm>
#include <cstdint>
#include <string>
#include <string_view>
#include <utility>
#include <vector>

#include "common/arena.h"
#include "common/diagnostic.h"
#include "elaborator/type_eval.h"
#include "parser/ast.h"
#include "simulator/class_object.h"
#include "simulator/eval_array.h"
#include "simulator/eval_expr_internal.h"
#include "simulator/evaluation.h"
#include "simulator/scheduler.h"
#include "simulator/sim_context.h"
#include "simulator/statement_assign_internal.h"

namespace delta {

// Defined below; forward-declared so the queue-write helpers above its
// definition can call it. The default argument lives on the definition.
static int64_t EvalQueueIndex(const Expr* expr, QueueObject* q, SimContext& ctx,
                              Arena& arena, bool* has_xz);

void BuildLhsName(const Expr* expr, std::string& out) {
  if (expr->kind == ExprKind::kIdentifier) {
    if (!expr->scope_prefix.empty()) {
      out += expr->scope_prefix;
      out += ".";
    }
    out += expr->text;
    return;
  }
  if (expr->kind == ExprKind::kMemberAccess) {
    BuildLhsName(expr->lhs, out);
    out += ".";
    BuildLhsName(expr->rhs, out);
  }
}

Variable* TryResolveArrayElement(const Expr* lhs, SimContext& ctx) {
  if (lhs->kind != ExprKind::kSelect || !lhs->base || !lhs->index)
    return nullptr;
  if (lhs->base->kind != ExprKind::kIdentifier) return nullptr;
  if (lhs->index_end) return nullptr;
  auto idx = EvalExpr(lhs->index, ctx, ctx.GetArena());
  // An x or z bit anywhere in the index makes it invalid; an invalid-index
  // write is a no-op, so fail to resolve the element just as an out-of-range
  // index does.
  if (HasUnknownBits(idx)) return nullptr;
  auto elem_name =
      std::string(lhs->base->text) + "[" + std::to_string(idx.ToUint64()) + "]";
  return ctx.FindVariable(elem_name);
}

bool BuildCompoundLhsName(const Expr* expr, SimContext& ctx, Arena& arena,
                          std::string& name) {
  if (expr->kind == ExprKind::kIdentifier) {
    name = expr->text;
    return true;
  }
  if (expr->kind != ExprKind::kSelect || expr->index_end) return false;
  if (!BuildCompoundLhsName(expr->base, ctx, arena, name)) return false;
  auto idx_val = EvalExpr(expr->index, ctx, arena);
  // A dimension indexed with an x or z bit is invalid; refuse to build a name
  // for it so the surrounding write resolves to nothing and is a no-op.
  if (HasUnknownBits(idx_val)) return false;
  name += "[" + std::to_string(idx_val.ToUint64()) + "]";
  return true;
}

Variable* TryResolveCompoundElement(const Expr* lhs, SimContext& ctx,
                                    Arena& arena) {
  if (lhs->kind != ExprKind::kSelect || !lhs->base) return nullptr;
  if (lhs->base->kind != ExprKind::kSelect) return nullptr;
  if (lhs->index_end) return nullptr;
  std::string compound;
  if (!BuildCompoundLhsName(lhs, ctx, arena, compound)) return nullptr;
  auto* var = ctx.FindVariable(compound);
  if (var) return var;
  return ctx.CreateVariable(*arena.Create<std::string>(std::move(compound)),
                            32);
}

Variable* ResolveLhsVariable(const Expr* lhs, SimContext& ctx) {
  if (lhs->kind == ExprKind::kIdentifier) return ctx.FindVariable(lhs->text);
  if (lhs->kind == ExprKind::kMemberAccess) {
    std::string name;
    BuildLhsName(lhs, name);
    auto resolved = StripRootPrefix(name);
    return ctx.FindVariable(resolved);
  }
  if (lhs->kind == ExprKind::kSelect && lhs->base) {
    return ResolveLhsVariable(lhs->base, ctx);
  }
  return nullptr;
}

// Checks the tagged-union tag against the field being written. Returns true
// (with an emitted error) when the write targets a member that does not match
// the union's current tag; the caller treats that as a handled no-op write.
static bool TaggedUnionTagMismatch(std::string_view base_name,
                                   std::string_view field_name,
                                   SimContext& ctx) {
  auto tag = ctx.GetVariableTag(base_name);
  if (tag.empty()) return false;
  auto top = field_name;
  auto subdot = top.find('.');
  if (subdot != std::string_view::npos) top = top.substr(0, subdot);
  if (tag == top) return false;
  ctx.GetDiag().Error(
      {}, "run-time error: assigning member '" + std::string(field_name) +
              "' of tagged union '" + std::string(base_name) +
              "' which currently has tag '" + std::string(tag) + "'");
  return true;
}

// Writes a packed struct/union member into base_var when field_name names one
// of info's fields. Returns true when the field was found and written.
static bool WriteStructFieldBits(Variable* base_var, const StructTypeInfo* info,
                                 std::string_view field_name,
                                 const Logic4Vec& rhs_val) {
  uint32_t bit_offset = 0;
  uint32_t width = 0;
  if (!ResolveStructFieldPath(info, field_name, &bit_offset, &width)) {
    return false;
  }
  DepositBitField(base_var->value, bit_offset, rhs_val, width);
  base_var->NotifyWatchers();
  return true;
}

// Writes `field` onto class object `obj`, honoring declared-type scoping
// (§8.15) when the type is known so a base field is written rather than a
// shadowing derived one.
static void SetClassField(ClassObject* obj, const ClassTypeInfo* declared_type,
                          std::string_view field, const Logic4Vec& rhs_val) {
  if (declared_type)
    obj->SetPropertyForType(field, declared_type, rhs_val);
  else
    obj->SetProperty(std::string(field), rhs_val);
}

// Writes a (possibly chained) field path into class object `obj`. A chained
// path `first.rest` (e.g. `a.val`) fetches `first` as a class handle and
// recurses into the referenced object, so `o2.a.val = 88` reaches the same
// Inner object shared by a shallow copy (§8.12) rather than creating a flat
// "a.val" key on the outer object. Mirrors ResolveClassFieldChain on the read
// side; the inner fields carry no declared-type shadowing context. When `first`
// is not a live handle, the whole dotted path falls back to a flattened key
// (the legacy nested-handle storage scheme).
static void WriteClassFieldChain(ClassObject* obj,
                                 const ClassTypeInfo* declared_type,
                                 std::string_view field_path,
                                 const Logic4Vec& rhs_val, SimContext& ctx) {
  auto dot = field_path.find('.');
  if (dot == std::string_view::npos) {
    SetClassField(obj, declared_type, field_path, rhs_val);
    return;
  }
  auto& arena = ctx.GetArena();
  auto first = field_path.substr(0, dot);
  auto rest = field_path.substr(dot + 1);
  Logic4Vec handle_val =
      declared_type ? obj->GetPropertyForType(first, declared_type, arena)
                    : obj->GetProperty(first, arena);
  auto* next_obj = ctx.GetClassObject(handle_val.ToUint64());
  if (!next_obj) {
    SetClassField(obj, declared_type, field_path, rhs_val);
    return;
  }
  WriteClassFieldChain(next_obj, nullptr, rest, rhs_val, ctx);
}

// Writes field_name into the class object referenced by base_var. Returns true
// when base_var refers to a live class object (the write is always performed in
// that case).
static bool WriteClassObjectField(Variable* base_var,
                                  std::string_view base_name,
                                  std::string_view field_name,
                                  const Logic4Vec& rhs_val, SimContext& ctx) {
  auto handle = base_var->value.ToUint64();
  auto* obj = ctx.GetClassObject(handle);
  if (!obj) return false;
  const ClassTypeInfo* declared_type = nullptr;
  auto declared = ctx.GetVariableClassType(base_name);
  if (!declared.empty()) declared_type = ctx.FindClassType(declared);
  WriteClassFieldChain(obj, declared_type, field_name, rhs_val, ctx);
  base_var->NotifyWatchers();
  return true;
}

// Writes field_name into the current `this` object. *handled is set true when
// base_name names `this`; in that case the returned value is the write result.
static bool WriteThisField(std::string_view base_name,
                           std::string_view field_name,
                           const Logic4Vec& rhs_val, SimContext& ctx,
                           bool* handled) {
  *handled = false;
  if (base_name != "this") return false;
  *handled = true;
  auto* self = ctx.CurrentThis();
  if (!self) return false;
  self->SetProperty(std::string(field_name), rhs_val);
  return true;
}

// Writes field_name into the parent slice of the current `this` object via
// `super`. *handled is set true when base_name names `super`.
static bool WriteSuperField(std::string_view base_name,
                            std::string_view field_name,
                            const Logic4Vec& rhs_val, SimContext& ctx,
                            bool* handled) {
  *handled = false;
  if (base_name != "super") return false;
  *handled = true;
  auto* self = ctx.CurrentThis();
  if (!(self && self->type && self->type->parent)) return false;
  self->SetPropertyForType(std::string(field_name), self->type->parent,
                           rhs_val);
  return true;
}

// Writes field_name as a static property of the class named base_name.
// *handled is set true when base_name names a known class type.
static bool WriteStaticClassField(std::string_view base_name,
                                  std::string_view field_name,
                                  const Logic4Vec& rhs_val, SimContext& ctx,
                                  bool* handled) {
  *handled = false;
  auto* cls_type = ctx.FindClassType(base_name);
  if (!cls_type) return false;
  *handled = true;
  auto sit = cls_type->static_properties.find(std::string(field_name));
  if (sit == cls_type->static_properties.end()) return false;
  sit->second = rhs_val;
  return true;
}

// Writes field_name into the variable named base_name, which may be a packed
// struct/union or a class-object handle. The caller has confirmed base_name is
// neither this/super nor a class type.
static bool WriteVariableField(std::string_view base_name,
                               std::string_view field_name,
                               const Logic4Vec& rhs_val, SimContext& ctx) {
  auto* base_var = ctx.FindVariable(base_name);
  if (!base_var) return false;
  auto* info = ctx.GetVariableStructType(base_name);
  if (info) {
    if (info->is_union && TaggedUnionTagMismatch(base_name, field_name, ctx)) {
      return true;
    }
    if (WriteStructFieldBits(base_var, info, field_name, rhs_val)) return true;
  }
  return WriteClassObjectField(base_var, base_name, field_name, rhs_val, ctx);
}

bool WriteStructField(const Expr* lhs, const Logic4Vec& rhs_val,
                      SimContext& ctx) {
  std::string name;
  BuildLhsName(lhs, name);
  auto dot = name.find('.');
  if (dot == std::string::npos) return false;
  auto base_name = std::string_view(name).substr(0, dot);
  auto field_name = std::string_view(name).substr(dot + 1);

  bool handled = false;
  bool result = WriteThisField(base_name, field_name, rhs_val, ctx, &handled);
  if (handled) return result;
  result = WriteSuperField(base_name, field_name, rhs_val, ctx, &handled);
  if (handled) return result;
  result = WriteStaticClassField(base_name, field_name, rhs_val, ctx, &handled);
  if (handled) return result;
  return WriteVariableField(base_name, field_name, rhs_val, ctx);
}

static void WritePartSelect(Variable* var, uint32_t lo, uint32_t width,
                            const Logic4Vec& rhs_val, Arena& arena) {
  uint64_t mask = (width >= 64) ? ~uint64_t{0} : (uint64_t{1} << width) - 1;
  uint64_t old_val = var->value.ToUint64();
  uint64_t new_bits = (rhs_val.ToUint64() & mask) << lo;
  uint64_t cleared = old_val & ~(mask << lo);
  var->value = MakeLogic4VecVal(arena, var->value.width, cleared | new_bits);
}

// §7.4.1: writes a single-index target on a packed multidimensional array as an
// outermost element (the inner-dimension width), not a single bit. Returns true
// when `var` is such an array and the write was handled.
static bool TryWritePackedElement(Variable* var, uint32_t idx,
                                  const Logic4Vec& rhs_val, Arena& arena) {
  if (var->packed_elem_width <= 1) return false;
  uint32_t w = var->packed_elem_width;
  uint64_t off = (idx >= var->packed_outer_lo)
                     ? (idx - var->packed_outer_lo) * uint64_t{w}
                     : 0;
  if (off < var->value.width)
    WritePartSelect(var, static_cast<uint32_t>(off), w, rhs_val, arena);
  return true;
}

void WriteBitSelect(Variable* var, const Expr* lhs, const Logic4Vec& rhs_val,
                    SimContext& ctx, Arena& arena) {
  auto idx_val = EvalExpr(lhs->index, ctx, arena);
  if (HasUnknownBits(idx_val)) return;
  auto idx = static_cast<uint32_t>(idx_val.ToUint64());
  if (!lhs->index_end) {
    if (TryWritePackedElement(var, idx, rhs_val, arena)) return;
    if (idx >= var->value.width) return;
    uint64_t old_val = var->value.ToUint64();
    uint64_t bit = rhs_val.ToUint64() & 1;
    uint64_t cleared = old_val & ~(uint64_t{1} << idx);
    var->value =
        MakeLogic4VecVal(arena, var->value.width, cleared | (bit << idx));
    return;
  }

  uint32_t lo = idx;
  auto end_val =
      static_cast<uint32_t>(EvalExpr(lhs->index_end, ctx, arena).ToUint64());
  uint32_t w = end_val;
  if (lhs->is_part_select_plus) {
  } else if (lhs->is_part_select_minus) {
    lo = (idx >= w - 1) ? idx - w + 1 : 0;
  } else {
    lo = std::min(idx, end_val);
    w = std::max(idx, end_val) - lo + 1;
  }
  if (w == 0) {
    ctx.GetDiag().Error({}, "zero-width part-select is not allowed");
    return;
  }
  if (lo >= var->value.width) return;
  if (lo + w > var->value.width) w = var->value.width - lo;
  WritePartSelect(var, lo, w, rhs_val, arena);
}

// Single-word resize for known (no x/z) values that fit in 64 bits, applying
// sign extension when the source is signed and being widened.
static Logic4Vec ResizeNarrowKnown(const Logic4Vec& val, uint32_t target_width,
                                   Arena& arena) {
  uint64_t v = val.ToUint64();
  if (val.is_signed && target_width > val.width && val.width > 0 &&
      val.width < 64) {
    uint64_t sign_bit = uint64_t{1} << (val.width - 1);
    if (v & sign_bit) v |= ~uint64_t{0} << val.width;
  }
  return MakeLogic4VecVal(arena, target_width, v);
}

// Replicates the source MSB across the widened high bits of result when val is
// signed and being widened past its original width.
static void SignExtendWideResult(const Logic4Vec& val, uint32_t target_width,
                                 Logic4Vec& result) {
  if (!val.is_signed || target_width <= val.width || val.width == 0) return;
  uint32_t msb_idx = (val.width - 1) / 64;
  uint64_t msb_mask = uint64_t{1} << ((val.width - 1) % 64);
  uint64_t a_fill = (val.words[msb_idx].aval & msb_mask) ? ~uint64_t{0} : 0;
  uint64_t b_fill = (val.words[msb_idx].bval & msb_mask) ? ~uint64_t{0} : 0;
  if (!(a_fill || b_fill)) return;
  uint32_t fill_bit = val.width % 64;
  if (fill_bit != 0) {
    uint64_t fill_mask = ~((uint64_t{1} << fill_bit) - 1);
    uint32_t target_bits_in_word = target_width % 64;
    if (target_bits_in_word > fill_bit) {
      uint64_t upper_limit = (uint64_t{1} << target_bits_in_word) - 1;
      fill_mask &= upper_limit;
    }
    result.words[val.width / 64].aval |= a_fill & fill_mask;
    result.words[val.width / 64].bval |= b_fill & fill_mask;
  }
  uint32_t first_full = val.width / 64 + (fill_bit != 0 ? 1 : 0);
  for (uint32_t i = first_full; i < result.nwords; ++i) {
    result.words[i].aval = a_fill;
    result.words[i].bval = b_fill;
  }
}

// Clears any bits above target_width in the final (partial) word of result.
static void MaskHighBits(uint32_t target_width, Logic4Vec& result) {
  uint32_t last_bit = target_width % 64;
  if (last_bit == 0) return;
  uint32_t last_word = (target_width - 1) / 64;
  uint64_t mask = (uint64_t{1} << last_bit) - 1;
  result.words[last_word].aval &= mask;
  result.words[last_word].bval &= mask;
}

Logic4Vec ResizeToWidth(Logic4Vec val, uint32_t target_width, Arena& arena) {
  if (val.width == target_width || target_width == 0) return val;

  bool has_xz = false;
  for (uint32_t i = 0; i < val.nwords && !has_xz; ++i)
    has_xz = val.words[i].bval != 0;

  if (!has_xz && val.width <= 64 && target_width <= 64)
    return ResizeNarrowKnown(val, target_width, arena);

  auto result = MakeLogic4Vec(arena, target_width);
  result.is_signed = val.is_signed;
  uint32_t copy_words = std::min(val.nwords, result.nwords);
  for (uint32_t i = 0; i < copy_words; ++i) {
    result.words[i].aval = val.words[i].aval;
    result.words[i].bval = val.words[i].bval;
  }
  SignExtendWideResult(val, target_width, result);
  MaskHighBits(target_width, result);
  return result;
}

static void CopyArrayElements(std::string_view dst_name, const ArrayInfo& dst,
                              std::string_view src_name, const ArrayInfo& src,
                              SimContext& ctx) {
  uint32_t n = std::min(dst.size, src.size);
  for (uint32_t i = 0; i < n; ++i) {
    uint32_t si =
        src.is_descending ? (src.lo + src.size - 1 - i) : (src.lo + i);
    uint32_t di =
        dst.is_descending ? (dst.lo + dst.size - 1 - i) : (dst.lo + i);
    auto sn = std::string(src_name) + "[" + std::to_string(si) + "]";
    auto dn = std::string(dst_name) + "[" + std::to_string(di) + "]";
    auto* sv = ctx.FindVariable(sn);
    auto* dv = ctx.FindVariable(dn);
    if (sv && dv) {
      dv->value = sv->value;
      dv->NotifyWatchers();
    }
  }
}

bool IsTypeKeyword(std::string_view key) {
  return key == "int" || key == "integer" || key == "logic" || key == "reg" ||
         key == "byte" || key == "shortint" || key == "longint" ||
         key == "bit" || key == "real" || key == "shortreal" || key == "time" ||
         key == "realtime" || key == "string";
}

bool TypeKeyMatchesKind(std::string_view key, DataTypeKind kind) {
  switch (kind) {
    case DataTypeKind::kInt:
      return key == "int";
    case DataTypeKind::kInteger:
      return key == "integer";
    case DataTypeKind::kLogic:
      return key == "logic";
    case DataTypeKind::kReg:
      return key == "reg";
    case DataTypeKind::kByte:
      return key == "byte";
    case DataTypeKind::kShortint:
      return key == "shortint";
    case DataTypeKind::kLongint:
      return key == "longint";
    case DataTypeKind::kBit:
      return key == "bit";
    case DataTypeKind::kReal:
      return key == "real";
    case DataTypeKind::kShortreal:
      return key == "shortreal";
    case DataTypeKind::kTime:
      return key == "time";
    case DataTypeKind::kRealtime:
      return key == "realtime";
    case DataTypeKind::kString:
      return key == "string";
    default:
      return false;
  }
}

// Finds the pattern element whose explicit integer key equals idx. Returns the
// matching element index, or rhs->elements.size() when none matches.
static size_t FindIndexKeyedElement(const Expr* rhs, uint32_t idx) {
  for (size_t i = 0; i < rhs->pattern_keys.size(); ++i) {
    if (i >= rhs->elements.size()) break;
    auto& key = rhs->pattern_keys[i];
    if (key == "default" || IsTypeKeyword(key)) continue;
    if (static_cast<uint32_t>(std::stoul(std::string(key))) == idx) return i;
  }
  return rhs->elements.size();
}

// Finds the pattern element keyed by a type keyword matching elem_type. Returns
// the matching element index, or rhs->elements.size() when none matches.
static size_t FindTypeKeyedElement(const Expr* rhs, DataTypeKind elem_type) {
  for (size_t i = 0; i < rhs->pattern_keys.size(); ++i) {
    if (i >= rhs->elements.size()) break;
    auto& key = rhs->pattern_keys[i];
    if (IsTypeKeyword(key) && TypeKeyMatchesKind(key, elem_type)) return i;
  }
  return rhs->elements.size();
}

// Finds the pattern element keyed by "default". Returns the matching element
// index, or rhs->elements.size() when none matches.
static size_t FindDefaultKeyedElement(const Expr* rhs) {
  for (size_t i = 0; i < rhs->pattern_keys.size(); ++i) {
    if (i >= rhs->elements.size()) break;
    if (rhs->pattern_keys[i] == "default") return i;
  }
  return rhs->elements.size();
}

// One element slot of the unpacked-array target of an assignment pattern
// (IEEE 1800 §7.6 / §10.9.2). `idx` is the array index being filled; `width`
// and `elem_type_kind` mirror the element-type fields of the target's
// ArrayInfo and select default/type-keyed pattern members.
namespace {
struct PatternArrayElem {
  uint32_t idx;
  uint32_t width;
  DataTypeKind elem_type_kind;
};
}  // namespace

static Logic4Vec FindArrayKeyedValue(const Expr* rhs,
                                     const PatternArrayElem& slot,
                                     SimContext& ctx, Arena& arena) {
  size_t match = FindIndexKeyedElement(rhs, slot.idx);
  if (match >= rhs->elements.size())
    match = FindTypeKeyedElement(rhs, slot.elem_type_kind);
  if (match >= rhs->elements.size()) match = FindDefaultKeyedElement(rhs);
  if (match < rhs->elements.size())
    return EvalExpr(rhs->elements[match], ctx, arena);
  return MakeLogic4VecVal(arena, slot.width, 0);
}

namespace {
// §7.4.2: bundle for distributing a (possibly nested) assignment pattern into a
// fixed multidimensional unpacked array, keeping the recursive walk within the
// parameter-count limit.
struct PatternDist {
  const ArrayInfo& info;
  SimContext& ctx;
  Arena& arena;
};
}  // namespace

// §10.9.1: the pattern element that fills one dimension's element at index
// `idx` (position `pos`): a positional element, an index-keyed element, or the
// default-keyed element. Null when the pattern supplies none for this element.
static const Expr* SelectDimElement(const Expr* pat, uint32_t idx,
                                    uint32_t pos) {
  if (pat->pattern_keys.empty()) {
    // §10.9.1: a replication in an array pattern stands for an entire single
    // dimension. Expand its body positionally across this dimension so each of
    // the N copies lands on successive elements (e.g. '{2{'{3{y}}}} fills a
    // [_:_][_:_] array with y at every leaf) instead of leaking the replicate
    // node out as one scalar.
    if (pat->elements.size() == 1 &&
        pat->elements[0]->kind == ExprKind::kReplicate) {
      const auto& body = pat->elements[0]->elements;
      return body.empty() ? nullptr : body[pos % body.size()];
    }
    return pos < pat->elements.size() ? pat->elements[pos] : nullptr;
  }
  size_t m = FindIndexKeyedElement(pat, idx);
  if (m >= pat->elements.size()) m = FindDefaultKeyedElement(pat);
  return m < pat->elements.size() ? pat->elements[m] : nullptr;
}

// Writes one scalar leaf element (resizing/defaulting to the element width).
static void WriteLeaf(const PatternDist& pd, const std::string& name,
                      const Expr* sub) {
  auto* elem = pd.ctx.FindVariable(name);
  if (!elem) return;
  Logic4Vec val = sub ? EvalExpr(sub, pd.ctx, pd.arena)
                      : MakeLogic4VecVal(pd.arena, pd.info.elem_width, 0);
  elem->value = ResizeToWidth(val, pd.info.elem_width, pd.arena);
  elem->NotifyWatchers();
}

// §10.9.1: broadcasts one scalar `sub` to every leaf at and below dimension `d`
// of the subtree rooted at `prefix` (an inner default that is not itself a
// nested pattern fills the whole sub-array).
static void WriteScalarSubtree(const PatternDist& pd, const std::string& prefix,
                               size_t d, const Expr* sub) {
  uint32_t lo = pd.info.dim_los[d];
  bool last = (d + 1 == pd.info.dim_sizes.size());
  for (uint32_t i = 0; i < pd.info.dim_sizes[d]; ++i) {
    std::string child = prefix + "[" + std::to_string(lo + i) + "]";
    if (last)
      WriteLeaf(pd, child, sub);
    else
      WriteScalarSubtree(pd, child, d + 1, sub);
  }
}

// §7.4.2/§10.9.1: distribute the assignment pattern `pat` across dimension `d`
// of the subtree rooted at `prefix`. A nested pattern recurses into the next
// dimension; a scalar at a non-last dimension broadcasts to the sub-array.
static void DistributeDimPattern(const PatternDist& pd,
                                 const std::string& prefix, size_t d,
                                 const Expr* pat) {
  uint32_t lo = pd.info.dim_los[d];
  bool last = (d + 1 == pd.info.dim_sizes.size());
  for (uint32_t i = 0; i < pd.info.dim_sizes[d]; ++i) {
    std::string child = prefix + "[" + std::to_string(lo + i) + "]";
    const Expr* sub = SelectDimElement(pat, lo + i, i);
    bool is_pattern = sub && (sub->kind == ExprKind::kAssignmentPattern ||
                              sub->kind == ExprKind::kConcatenation);
    if (last)
      WriteLeaf(pd, child, sub);
    else if (is_pattern)
      DistributeDimPattern(pd, child, d + 1, sub);
    else
      WriteScalarSubtree(pd, child, d + 1, sub);
  }
}

static void DistributePatternToArray(std::string_view arr_name,
                                     const ArrayInfo& info, const Expr* rhs,
                                     SimContext& ctx, Arena& arena) {
  if (info.dim_sizes.size() > 1) {
    DistributeDimPattern(PatternDist{info, ctx, arena}, std::string(arr_name),
                         0, rhs);
    return;
  }
  bool named = !rhs->pattern_keys.empty();
  bool replicate = rhs->elements.size() == 1 &&
                   rhs->elements[0]->kind == ExprKind::kReplicate;
  uint32_t inner_count =
      replicate ? static_cast<uint32_t>(rhs->elements[0]->elements.size()) : 0;
  for (uint32_t i = 0; i < info.size; ++i) {
    uint32_t idx =
        info.is_descending ? (info.lo + info.size - 1 - i) : (info.lo + i);
    auto name = std::string(arr_name) + "[" + std::to_string(idx) + "]";
    auto* elem = ctx.FindVariable(name);
    if (!elem) continue;
    if (named) {
      PatternArrayElem slot{idx, info.elem_width, info.elem_type_kind};
      elem->value = ResizeToWidth(FindArrayKeyedValue(rhs, slot, ctx, arena),
                                  info.elem_width, arena);
    } else if (replicate && inner_count > 0) {
      auto val =
          EvalExpr(rhs->elements[0]->elements[i % inner_count], ctx, arena);
      elem->value = ResizeToWidth(val, info.elem_width, arena);
    } else if (i < rhs->elements.size()) {
      auto val = EvalExpr(rhs->elements[i], ctx, arena);
      elem->value = ResizeToWidth(val, info.elem_width, arena);
    } else {
      elem->value = MakeLogic4VecVal(arena, info.elem_width, 0);
    }
    elem->NotifyWatchers();
  }
}

static void CollectFixedArrayElements(std::string_view name,
                                      const ArrayInfo& ai, SimContext& ctx,
                                      std::vector<Logic4Vec>& out);

// §10.10: an element of an unpacked array concatenation may itself be an
// assignment pattern that contributes its elements (not a single value),
// either bare ('{...}) or typed (AI3'{5, 6, 7}). The typed form parses as a
// cast wrapping the pattern, so unwrap it here.
static const Expr* AsArrayConcatPattern(const Expr* item) {
  if (item->kind == ExprKind::kAssignmentPattern) return item;
  if (item->kind == ExprKind::kCast && item->lhs &&
      item->lhs->kind == ExprKind::kAssignmentPattern)
    return item->lhs;
  return nullptr;
}

static std::vector<Logic4Vec> CollectConcatElements(const Expr* rhs,
                                                    SimContext& ctx,
                                                    Arena& arena) {
  std::vector<Logic4Vec> elems;
  for (auto* item : rhs->elements) {
    if (item->kind == ExprKind::kIdentifier) {
      auto* ai = ctx.FindArrayInfo(item->text);
      if (ai) {
        CollectFixedArrayElements(item->text, *ai, ctx, elems);
        continue;
      }
      auto* q = ctx.FindQueue(item->text);
      if (q) {
        elems.insert(elems.end(), q->elements.begin(), q->elements.end());
        continue;
      }
    }
    if (const Expr* pat = AsArrayConcatPattern(item)) {
      for (auto* elem : pat->elements) {
        elems.push_back(EvalExpr(elem, ctx, arena));
      }
      continue;
    }
    elems.push_back(EvalExpr(item, ctx, arena));
  }
  return elems;
}

static void DistributeConcatToArray(std::string_view arr_name,
                                    const ArrayInfo& info, const Expr* rhs,
                                    SimContext& ctx, Arena& arena) {
  auto elems = CollectConcatElements(rhs, ctx, arena);
  if (elems.size() != info.size) {
    ctx.GetDiag().Error(
        {}, "unpacked array concatenation size mismatch: expected " +
                std::to_string(info.size) + " elements, got " +
                std::to_string(elems.size()));
    return;
  }
  for (uint32_t i = 0; i < info.size; ++i) {
    uint32_t idx =
        info.is_descending ? (info.lo + info.size - 1 - i) : (info.lo + i);
    auto name = std::string(arr_name) + "[" + std::to_string(idx) + "]";
    auto* elem = ctx.FindVariable(name);
    if (!elem) continue;
    elem->value = ResizeToWidth(elems[i], info.elem_width, arena);
    elem->NotifyWatchers();
  }
}

// Copies the resizable (queue) source elements into the fixed/dynamic array
// destination dst named dst_name, element by element.
static void CopyResizableSourceToArray(std::string_view dst_name,
                                       const ArrayInfo& dst,
                                       const QueueObject& src_q,
                                       uint32_t src_size, SimContext& ctx) {
  uint32_t n = std::min(dst.size, src_size);
  for (uint32_t i = 0; i < n; ++i) {
    uint32_t di =
        dst.is_descending ? (dst.lo + dst.size - 1 - i) : (dst.lo + i);
    auto dn = std::string(dst_name) + "[" + std::to_string(di) + "]";
    auto* dv = ctx.FindVariable(dn);
    if (dv) {
      dv->value = src_q.elements[i];
      dv->NotifyWatchers();
    }
  }
}

// Handles "array = identifier" where the destination names an array. Sets
// *handled to true and returns true/false matching the caller's return value
// when the destination is an array; leaves *handled false (fall through) when
// the destination is not an array.
static bool TryArrayIdentifierCopy(const Stmt* stmt, SimContext& ctx,
                                   bool* handled) {
  *handled = false;
  auto* dst = ctx.FindArrayInfo(stmt->lhs->text);
  if (!dst) return false;
  *handled = true;
  auto* src = ctx.FindArrayInfo(stmt->rhs->text);
  auto* src_q = ctx.FindQueue(stmt->rhs->text);
  bool src_is_aggregate = (src != nullptr) || (src_q != nullptr);
  if (!src_is_aggregate) return false;
  bool src_resizable = src_q != nullptr;
  uint32_t src_size =
      src_resizable ? static_cast<uint32_t>(src_q->elements.size()) : src->size;

  if (!dst->is_dynamic && !dst->is_queue && src_resizable &&
      dst->size != src_size) {
    ctx.GetDiag().Error(
        {}, "array size mismatch in assignment to fixed-size array");
    return true;
  }
  if (src_resizable) {
    CopyResizableSourceToArray(stmt->lhs->text, *dst, *src_q, src_size, ctx);
    return true;
  }
  CopyArrayElements(stmt->lhs->text, *dst, stmt->rhs->text, *src, ctx);
  return true;
}

bool TryArrayBlockingAssign(const Stmt* stmt, SimContext& ctx, Arena& arena) {
  if (stmt->lhs->kind != ExprKind::kIdentifier) return false;
  if (stmt->rhs && stmt->rhs->kind == ExprKind::kAssignmentPattern) {
    auto* ainfo = ctx.FindArrayInfo(stmt->lhs->text);
    if (ainfo) {
      DistributePatternToArray(stmt->lhs->text, *ainfo, stmt->rhs, ctx, arena);
      return true;
    }
  }

  if (stmt->rhs && stmt->rhs->kind == ExprKind::kConcatenation) {
    auto* ainfo = ctx.FindArrayInfo(stmt->lhs->text);
    if (ainfo) {
      DistributeConcatToArray(stmt->lhs->text, *ainfo, stmt->rhs, ctx, arena);
      return true;
    }
  }
  if (stmt->rhs->kind == ExprKind::kIdentifier) {
    bool handled = false;
    bool result = TryArrayIdentifierCopy(stmt, ctx, &handled);
    if (handled) return result;
  }
  return false;
}

bool TryAssocIndexedWrite(const Expr* lhs, const Logic4Vec& rhs_val,
                          SimContext& ctx, Arena& arena) {
  if (!lhs->base || lhs->base->kind != ExprKind::kIdentifier) return false;
  auto* aa = ctx.FindAssocArray(lhs->base->text);
  if (!aa || !lhs->index) return false;
  if (aa->is_string_key) {
    auto key_vec = EvalExpr(lhs->index, ctx, arena);
    uint32_t nb = key_vec.width / 8;
    std::string s;
    s.reserve(nb);
    for (uint32_t i = nb; i > 0; --i) {
      uint32_t bi = i - 1;
      auto ch = static_cast<char>(
          (key_vec.words[(bi * 8) / 64].aval >> ((bi * 8) % 64)) & 0xFF);
      if (ch != 0) s.push_back(ch);
    }
    aa->str_data[s] = rhs_val;
  } else {
    auto key_val = EvalExpr(lhs->index, ctx, arena);
    if (HasUnknownBits(key_val)) {
      ctx.GetDiag().Warning({}, "associative array index contains x/z");
      return true;
    }
    auto key = AssocIntKey(key_val, aa->is_wildcard, aa->index_width,
                           aa->is_index_signed);
    aa->int_data[key] = rhs_val;
  }
  return true;
}

bool TryQueueIndexedWrite(const Expr* lhs, const Logic4Vec& rhs_val,
                          SimContext& ctx, Arena&) {
  if (!lhs->base || lhs->base->kind != ExprKind::kIdentifier) return false;
  auto* q = ctx.FindQueue(lhs->base->text);
  if (!q || !lhs->index) return false;
  auto& arena = ctx.GetArena();
  bool idx_xz = false;
  auto idx = EvalQueueIndex(lhs->index, q, ctx, arena, &idx_xz);

  if (idx_xz) {
    ctx.GetDiag().Warning({}, "queue write index contains x/z");
    return true;
  }
  auto sz = static_cast<int64_t>(q->elements.size());

  if (idx == sz) {
    bool has_room = (q->max_size < 0) ||
                    (static_cast<int32_t>(q->elements.size()) < q->max_size);
    if (has_room) {
      q->elements.push_back(rhs_val);
      q->element_ids.push_back(q->AllocateId());
      ++q->generation;
    } else {
      ctx.GetDiag().Warning({}, "bounded queue overflow in indexed write");
    }
    return true;
  }
  if (idx >= 0 && idx < sz) {
    q->elements[static_cast<size_t>(idx)] = rhs_val;
    return true;
  }

  ctx.GetDiag().Warning({}, "queue write index out of bounds");
  return true;
}

static int64_t EvalQueueIndex(const Expr* expr, QueueObject* q, SimContext& ctx,
                              Arena& arena, bool* has_xz = nullptr) {
  ctx.PushScope();
  auto* dv = ctx.CreateLocalVariable("$", 32);
  int64_t last =
      q->elements.empty() ? 0 : static_cast<int64_t>(q->elements.size()) - 1;
  dv->value = MakeLogic4VecVal(arena, 32, static_cast<uint64_t>(last));
  auto val = EvalExpr(expr, ctx, arena);
  ctx.PopScope();
  if (has_xz) *has_xz = HasUnknownBits(val);
  uint64_t raw = val.ToUint64();
  if (val.width > 0 && val.width < 64) {
    uint64_t sign = uint64_t{1} << (val.width - 1);
    if (raw & sign) raw |= ~uint64_t{0} << val.width;
  }
  return static_cast<int64_t>(raw);
}

static bool CollectFromQueueSlice(const Expr* expr, SimContext& ctx,
                                  Arena& arena, std::vector<Logic4Vec>& out) {
  if (expr->kind != ExprKind::kSelect || !expr->base || !expr->index_end)
    return false;
  if (expr->base->kind != ExprKind::kIdentifier) return false;
  auto* q = ctx.FindQueue(expr->base->text);
  if (!q) return false;
  bool lo_xz = false, hi_xz = false;
  auto lo = EvalQueueIndex(expr->index, q, ctx, arena, &lo_xz);
  auto hi = EvalQueueIndex(expr->index_end, q, ctx, arena, &hi_xz);

  if (lo_xz || hi_xz) return true;

  if (lo < 0) lo = 0;
  auto qsz = static_cast<int64_t>(q->elements.size());

  if (hi >= qsz) hi = qsz - 1;

  for (int64_t i = lo; i <= hi; ++i)
    out.push_back(q->elements[static_cast<size_t>(i)]);
  return true;
}

static bool CollectFromQueueElem(const Expr* expr, SimContext& ctx,
                                 Arena& arena, std::vector<Logic4Vec>& out) {
  if (expr->kind != ExprKind::kSelect || !expr->base || expr->index_end)
    return false;
  if (expr->base->kind != ExprKind::kIdentifier) return false;
  auto* q = ctx.FindQueue(expr->base->text);
  if (!q) return false;
  auto idx = EvalQueueIndex(expr->index, q, ctx, arena);
  if (idx >= 0 && static_cast<size_t>(idx) < q->elements.size())
    out.push_back(q->elements[static_cast<size_t>(idx)]);
  return true;
}

static void CollectFixedArrayElements(std::string_view name,
                                      const ArrayInfo& ai, SimContext& ctx,
                                      std::vector<Logic4Vec>& out) {
  for (uint32_t i = 0; i < ai.size; ++i) {
    uint32_t idx = ai.lo + i;
    auto ename = std::string(name) + "[" + std::to_string(idx) + "]";
    auto* v = ctx.FindVariable(ename);
    if (v) out.push_back(v->value);
  }
}

static void CollectQueueElements(const Expr* expr, SimContext& ctx,
                                 Arena& arena, std::vector<Logic4Vec>& out) {
  if (expr->kind == ExprKind::kConcatenation) {
    for (auto* elem : expr->elements)
      CollectQueueElements(elem, ctx, arena, out);
    return;
  }
  if (CollectFromQueueSlice(expr, ctx, arena, out)) return;
  if (CollectFromQueueElem(expr, ctx, arena, out)) return;
  if (expr->kind == ExprKind::kIdentifier) {
    auto* q = ctx.FindQueue(expr->text);
    if (q) {
      out.insert(out.end(), q->elements.begin(), q->elements.end());
      return;
    }

    auto* ai = ctx.FindArrayInfo(expr->text);
    if (ai) {
      CollectFixedArrayElements(expr->text, *ai, ctx, out);
      return;
    }
  }
  if (TryCollectLocatorResult(expr, ctx, arena, out)) return;
  out.push_back(EvalExpr(expr, ctx, arena));
}

static void CopyNewInit(const Expr* rhs, QueueObject* q,
                        const std::vector<Logic4Vec>& saved, SimContext& ctx) {
  if (rhs->args.size() < 2) return;
  auto* init_expr = rhs->args[1];
  if (!init_expr || init_expr->kind != ExprKind::kIdentifier) return;
  auto* src = ctx.FindQueue(init_expr->text);
  if (!src) return;

  const auto& src_elems = (src == q) ? saved : src->elements;
  size_t copy_len = std::min(q->elements.size(), src_elems.size());
  for (size_t i = 0; i < copy_len; ++i) q->elements[i] = src_elems[i];
}

bool TryQueueBlockingAssign(const Stmt* stmt, SimContext& ctx, Arena& arena) {
  if (stmt->lhs->kind != ExprKind::kIdentifier) return false;
  auto* q = ctx.FindQueue(stmt->lhs->text);
  if (!q) return false;
  if (stmt->rhs->kind == ExprKind::kConcatenation &&
      stmt->rhs->elements.empty()) {
    q->elements.clear();
    q->element_ids.clear();
    ++q->generation;
    return true;
  }
  if (stmt->rhs->kind == ExprKind::kCall && stmt->rhs->text == "new" &&
      !stmt->rhs->args.empty()) {
    auto sz_val = EvalExpr(stmt->rhs->args[0], ctx, arena);
    int64_t sz = SignExtend(sz_val.ToUint64(), sz_val.width);

    if (sz < 0) {
      ctx.GetDiag().Error({}, "dynamic array new[] size is negative");
      return true;
    }

    auto saved = q->elements;
    q->elements.resize(static_cast<size_t>(sz),
                       MakeLogic4VecVal(arena, q->elem_width, 0));
    CopyNewInit(stmt->rhs, q, saved, ctx);
    q->AssignFreshIds();
    ++q->generation;
    return true;
  }
  std::vector<Logic4Vec> elems;
  CollectQueueElements(stmt->rhs, ctx, arena, elems);
  if (q->max_size > 0 && static_cast<int32_t>(elems.size()) > q->max_size) {
    elems.resize(static_cast<size_t>(q->max_size));
    ctx.GetDiag().Warning({}, "bounded queue overflow in assignment");
  }
  q->elements = std::move(elems);
  q->AssignFreshIds();
  ++q->generation;
  return true;
}

}  // namespace delta
