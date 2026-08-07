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
#include "simulator/packed_select.h"
#include "simulator/scheduler.h"
#include "simulator/sim_context.h"
#include "simulator/statement_assign_internal.h"

namespace delta {

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
// `loc` is where the target was written: the names arrive as text rebuilt from
// the target expression, which carries the position they lost.
static bool TaggedUnionTagMismatch(std::string_view base_name,
                                   std::string_view field_name, SimContext& ctx,
                                   SourceLoc loc) {
  auto tag = ctx.GetVariableTag(base_name);
  if (tag.empty()) return false;
  auto top = field_name;
  auto subdot = top.find('.');
  if (subdot != std::string_view::npos) top = top.substr(0, subdot);
  if (tag == top) return false;
  ctx.GetDiag().Error(
      loc,
      "run-time error: assigning member '" + std::string(field_name) +
          "' of tagged union '" + std::string(base_name) +
          "' which currently has tag '" + std::string(tag) + "'",
      Subclause("11.9"));
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
                               const Logic4Vec& rhs_val, SimContext& ctx,
                               SourceLoc loc) {
  auto* base_var = ctx.FindVariable(base_name);
  if (!base_var) return false;
  auto* info = ctx.GetVariableStructType(base_name);
  if (info) {
    if (info->is_union &&
        TaggedUnionTagMismatch(base_name, field_name, ctx, loc)) {
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
  return WriteVariableField(base_name, field_name, rhs_val, ctx,
                            lhs->range.start);
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
static bool TryWritePackedElement(Variable* var, int64_t idx,
                                  const Logic4Vec& rhs_val, Arena& arena) {
  if (var->packed_elem_width <= 1) return false;
  auto range = var->DeclaredRange();
  if (!range.Contains(idx)) return true;
  uint32_t w = var->packed_elem_width;
  auto off = static_cast<uint64_t>(range.OffsetOf(idx)) * w;
  if (off < var->value.width)
    WritePartSelect(var, static_cast<uint32_t>(off), w, rhs_val, arena);
  return true;
}

void WriteBitSelect(Variable* var, const Expr* lhs, const Logic4Vec& rhs_val,
                    SimContext& ctx, Arena& arena) {
  auto idx_val = EvalExpr(lhs->index, ctx, arena);
  if (HasUnknownBits(idx_val)) return;
  auto idx = static_cast<int64_t>(idx_val.ToUint64());
  if (!lhs->index_end) {
    if (TryWritePackedElement(var, idx, rhs_val, arena)) return;
    auto range = var->BitSelectRange();
    if (!range.Contains(idx)) return;
    auto off = static_cast<uint32_t>(range.OffsetOf(idx));
    uint64_t old_val = var->value.ToUint64();
    uint64_t bit = rhs_val.ToUint64() & 1;
    uint64_t cleared = old_val & ~(uint64_t{1} << off);
    var->value =
        MakeLogic4VecVal(arena, var->value.width, cleared | (bit << off));
    return;
  }

  auto end_val =
      static_cast<int64_t>(EvalExpr(lhs->index_end, ctx, arena).ToUint64());
  auto target = PartSelectTargetIndices(lhs, idx, end_val);
  if (target.declared_width == 0) {
    ctx.GetDiag().Error(lhs->range.start,
                        "zero-width part-select is not allowed",
                        Subclause("11.5.1"));
    return;
  }
  auto bits =
      PartSelectStorageBits(var->BitSelectRange(), target.first, target.second);
  if (bits.width == 0) return;
  WritePartSelect(var, bits.lo, bits.width, rhs_val, arena);
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

void CopyArrayElements(std::string_view dst_name, const ArrayInfo& dst,
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

}  // namespace delta
