#include "simulator/statement_assign.h"

#include <algorithm>
#include <cstdint>
#include <string>
#include <string_view>
#include <utility>
#include <vector>

#include "common/arena.h"
#include "common/diagnostic.h"
#include "common/packed_range.h"
#include "elaborator/type_eval.h"
#include "parser/ast.h"
#include "simulator/assoc_element.h"
#include "simulator/class_object.h"
#include "simulator/eval_array.h"
#include "simulator/eval_expr_internal.h"
#include "simulator/evaluation.h"
#include "simulator/scheduler.h"
#include "simulator/sim_context.h"
#include "simulator/statement_assign_internal.h"
#include "simulator/variable.h"

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
// The declaring type is found by the walk SetPropertyForType makes for the same
// name, because a property declared on a base class is not in a derived type's
// own list.
static const ClassTypeInfo::PropertyInfo* FindPropertyInfo(
    const ClassTypeInfo* type, std::string_view name) {
  for (const auto* t = type; t != nullptr; t = t->parent) {
    for (const auto& prop : t->properties) {
      if (prop.name == name) return &prop;
    }
  }
  return nullptr;
}

Logic4Vec CoerceToPropertyType(const ClassTypeInfo* type, std::string_view name,
                               Logic4Vec val, Arena& arena) {
  const auto* prop = FindPropertyInfo(type, name);
  if (prop == nullptr || !prop->width_is_declared) return val;
  // ConvertRealForKnownLhs rather than ResizeToWidth: §6.12.1 converts a value
  // crossing the real boundary rather than reinterpreting its bits, and it
  // resizes everything that does not cross it.
  val = ConvertRealForKnownLhs(val, prop->is_real, prop->width, arena);
  if (!prop->is_4state && !prop->is_real) CoerceTo2State(val);
  // §6.11.3: the declaration's signedness belongs to the value stored in the
  // property. A variable keeps it on the Variable and a read consults it there;
  // a property is only its Logic4Vec, so a value that arrived signed would stay
  // signed in an unsigned property -- the signed literal 240 truncated into a
  // `bit [7:0]` reading -16 rather than 240.
  if (!prop->is_real) val.is_signed = prop->is_signed;
  return val;
}

static void SetClassField(ClassObject* obj, const ClassTypeInfo* declared_type,
                          std::string_view field, const Logic4Vec& rhs_val,
                          Arena& arena) {
  // A chained path that fell back to a flattened key names no property, so
  // FindPropertyInfo answers for none and the value is stored as it arrived.
  const ClassTypeInfo* start = declared_type ? declared_type : obj->type;
  Logic4Vec stored = CoerceToPropertyType(start, field, rhs_val, arena);
  if (declared_type)
    obj->SetPropertyForType(field, declared_type, stored);
  else
    obj->SetProperty(std::string(field), stored);
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
    SetClassField(obj, declared_type, field_path, rhs_val, ctx.GetArena());
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
    SetClassField(obj, declared_type, field_path, rhs_val, arena);
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
  self->SetProperty(
      std::string(field_name),
      CoerceToPropertyType(self->type, field_name, rhs_val, ctx.GetArena()));
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
                           CoerceToPropertyType(self->type->parent, field_name,
                                                rhs_val, ctx.GetArena()));
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
  sit->second =
      CoerceToPropertyType(cls_type, field_name, rhs_val, ctx.GetArena());
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
  // §7.8.7: `b[2].x = 5` names a member of an associative array element, which
  // the name built below cannot reach because the select contributes nothing
  // to it. Allocate the element and write the member through the array.
  if (TryWriteAssocMemberField(lhs, rhs_val, ctx, ctx.GetArena())) return true;
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

// Deposits `rhs_val` in the window of `var` that `bits` names. §11.5.1 has a
// part-select that is partly out of range "when written, only affect the bits
// that are in range", and which bits of the value the affected ones receive is
// bits.src_lo: a select running off the low end of its object has its own low
// bits land nowhere, so `a[1 -: 4] = 4'b1101` on a `logic [7:0] a` -- which the
// clause reads as `a[1:-2]` -- gives `a[1:0]` the value's bits [3:2] and must
// leave `a` at 8'h03. Taking the value's low bits whichever end the select ran
// off left it at 8'h01. The offset is zero for a select running off the high
// end, where the bits that land are the value's least significant ones.
//
// The window is deposited rather than computed in a machine word, because
// "only affect the bits that are in range" is a statement about every bit of
// the target the select did not name and not only about the ones beside it.
// Reading the target through Logic4Vec::ToUint64 and rebuilding it with
// MakeLogic4VecVal moved three sets of them. ToUint64 returns words[0] alone
// and MakeLogic4VecVal fills a fresh zeroed array, so a target wider than one
// word lost everything above bit 63: `w = '1; w[3:0] = 4'h0;` on a
// `logic [99:0] w` must leave 96 ones and left 60, w[99:64] being neither named
// by the select nor the value's to touch. ToUint64 returns `aval & ~bval` and
// MakeLogic4VecVal sets no bval, so the x and z that §6.3.1 lets every bit of a
// 4-state vector hold -- "All bits of 4-state vectors can be independently set
// to one of the four basic values", and §6.11.2 makes `logic` one of those
// types, whose values "have additional bits, which encode the x and z states"
// -- were read as 0 on the way in and stored as 0 on the way out:
// `a = 8'hxx; a[1:0] = 2'b11;` must read 8'bxxxxxx11 and read 8'b00000011, and
// `a = 8'h00; a[1:0] = 2'b1x;` must read 8'b0000001x and read 8'b00000010. And
// `mask << bits.lo` was undefined once the window began at bit 64 or above, the
// shift count being taken modulo 64 on x86-64, so `w[71:68] = 4'hF` on the same
// `logic [99:0] w` landed on w[7:4] and left w[71:68] at zero. DepositBitField
// is documented multi-word safe for a start bit of 64 or more, which answers
// the shift and the lost high words at once, and ExtractBitField takes the
// value's landing bits with their 4-state encoding kept, which answers the
// projection on the source side and makes bits.src_lo simply where the extract
// begins.
//
// The deposit is made into a fresh copy of the target's current value rather
// than through the words it is holding, for the reason WriteOwnedBits
// (statement_assign_decl.cpp) gives: copying a Logic4Vec copies its `words`
// pointer rather than the words (common/types.h), so a variable last written
// whole from another object shares that object's storage and an in-place
// deposit would write these bits into whatever else is holding it.
//
// §6.11.2 makes `bit` and `int` 2-state types that "do not have unknown
// values", so a 2-state target is coerced here explicitly. MakeLogic4VecVal
// gave that for free by never setting a bval; now that the deposit carries x
// and z, an x reaching such a target would otherwise survive.
void WritePartSelect(Variable* var, const PartSelectBits& bits,
                     const Logic4Vec& rhs_val, Arena& arena) {
  Logic4Vec updated = ExtractBitField(arena, var->value, 0, var->value.width);
  DepositBitField(updated, bits.lo,
                  ExtractBitField(arena, rhs_val, bits.src_lo, bits.width),
                  bits.width);
  var->value = updated;
  if (!var->is_4state) CoerceTo2State(var->value);
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
  // §7.4.1's element is addressed whole or not at all -- the index was found in
  // the declared range above -- so none of its bits falls below the range and
  // the source offset is zero.
  if (off < var->value.width)
    WritePartSelect(var, {static_cast<uint32_t>(off), w}, rhs_val, arena);
  return true;
}

PartSelectBits SelectStorageBits(const Variable& var, const Expr* sel,
                                 SimContext& ctx, Arena& arena) {
  auto idx_val = EvalExpr(sel->index, ctx, arena);
  if (HasUnknownBits(idx_val)) return {0, 0};
  auto idx = SelectBoundValue(idx_val);
  if (sel->index_end == nullptr) {
    if (var.packed_elem_width > 1) {
      PackedRange elems = var.DeclaredRange();
      if (!elems.Contains(idx)) return {0, 0};
      auto base = static_cast<uint32_t>(elems.OffsetOf(idx));
      return {base * var.packed_elem_width, var.packed_elem_width};
    }
    PackedRange range = var.BitSelectRange();
    if (!range.Contains(idx)) return {0, 0};
    return {static_cast<uint32_t>(range.OffsetOf(idx)), 1};
  }
  auto end_val = EvalExpr(sel->index_end, ctx, arena);
  if (HasUnknownBits(end_val)) return {0, 0};
  auto target = PartSelectTargetIndices(idx, SelectBoundValue(end_val),
                                        sel->is_part_select_plus,
                                        sel->is_part_select_minus);
  // §11.5.1 spells an indexed part-select's width out separately and requires
  // that it "shall be a positive constant", so a width of zero names no bit of
  // the object -- which is what a zero width from this function already means.
  // The pair PartSelectTargetIndices answers cannot say so on its own: it is
  // the two ends of a width the select does not have, and for `a[3 +: 0]` it is
  // the indices 3 and 2, which any declaration holding them resolves to the
  // two-bit window a[3:2]. WriteBitSelect, which resolves a statement's own
  // indices rather than asking here, reports that width as an error instead of
  // writing it; every other caller reads the zero this returns as the absence
  // it is.
  if (target.declared_width == 0) return {0, 0};
  return PartSelectStorageBits(var.BitSelectRange(), target.first,
                               target.second);
}

void WriteBitSelect(Variable* var, const Expr* lhs, const Logic4Vec& rhs_val,
                    SimContext& ctx, Arena& arena) {
  // §10.6.2: a force "shall override a procedural assignment ... until a
  // release procedural statement is executed on the variable". Naming a
  // bit-select or a part-select as the target does not take the statement out
  // of that class -- the clause's own "shall not be a bit-select or a
  // part-select of a variable" restricts what may be forced, not what a force
  // overrides -- so this declines as every whole-variable writer does. It is
  // the one place the statement form, the compound form, the increment, the
  // expression forms and the subroutine-body form all pass through.
  if (var->is_forced) return;
  auto idx_val = EvalExpr(lhs->index, ctx, arena);
  if (HasUnknownBits(idx_val)) return;
  auto idx = SelectBoundValue(idx_val);
  if (!lhs->index_end) {
    if (TryWritePackedElement(var, idx, rhs_val, arena)) return;
    auto range = var->BitSelectRange();
    if (!range.Contains(idx)) return;
    // §11.5.1's bit-select "extract[s] a particular bit from a vector", which
    // is the one-bit case of the window WritePartSelect deposits and not a
    // different write, so it is written once. Computed in a machine word here
    // as well, it moved the same three sets of bits the comment above that
    // function names, and `uint64_t{1} << off` was undefined for a bit at 64 or
    // above: `enable[64] = 1'b1;` on a `logic [64:0] enable` set enable[0].
    // The source offset is zero because the bit takes the value's own least
    // significant bit, which is what `rhs_val.ToUint64() & 1` took.
    auto off = static_cast<uint32_t>(range.OffsetOf(idx));
    WritePartSelect(var, {off, 1U}, rhs_val, arena);
    return;
  }

  auto end_val = SelectBoundValue(EvalExpr(lhs->index_end, ctx, arena));
  auto target = PartSelectTargetIndices(idx, end_val, lhs->is_part_select_plus,
                                        lhs->is_part_select_minus);
  if (target.declared_width == 0) {
    ctx.GetDiag().Error(lhs->range.start,
                        "zero-width part-select is not allowed",
                        Subclause("11.5.1"));
    return;
  }
  auto bits =
      PartSelectStorageBits(var->BitSelectRange(), target.first, target.second);
  if (bits.width == 0) return;
  WritePartSelect(var, bits, rhs_val, arena);
}

// Single-word resize for known (no x/z) values that fit in 64 bits, applying
// sign extension when the source is signed and being widened.
// Logic4Vec::is_signed carries the signedness §11.7 gives the value itself,
// which $signed and $unsigned set, so the result takes the flag from val
// instead of the false MakeLogic4VecVal leaves in place. ResizeToWidth sets
// that flag from val on its wide path, and a value resized here is stored
// beside those, so the two paths have to answer alike.
static Logic4Vec ResizeNarrowKnown(const Logic4Vec& val, uint32_t target_width,
                                   Arena& arena) {
  uint64_t v = val.ToUint64();
  if (val.is_signed && target_width > val.width && val.width > 0 &&
      val.width < 64) {
    uint64_t sign_bit = uint64_t{1} << (val.width - 1);
    if (v & sign_bit) v |= ~uint64_t{0} << val.width;
  }
  Logic4Vec result = MakeLogic4VecVal(arena, target_width, v);
  result.is_signed = val.is_signed;
  return result;
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
