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
#include "simulator/evaluation.h"
#include "simulator/scheduler.h"
#include "simulator/sim_context.h"

namespace delta {

// --- LHS resolution helpers ---

// Build a dotted name from a MemberAccess expression tree (e.g., "s.a.b").
void BuildLhsName(const Expr* expr, std::string& out) {
  if (expr->kind == ExprKind::kIdentifier) {
    out += expr->text;
    return;
  }
  if (expr->kind == ExprKind::kMemberAccess) {
    BuildLhsName(expr->lhs, out);
    out += ".";
    BuildLhsName(expr->rhs, out);
  }
}

// §7.4: Try to resolve an array element variable (e.g. "A[0]").
// Returns the element variable if found, null otherwise.
Variable* TryResolveArrayElement(const Expr* lhs, SimContext& ctx) {
  if (lhs->kind != ExprKind::kSelect || !lhs->base || !lhs->index)
    return nullptr;
  if (lhs->base->kind != ExprKind::kIdentifier) return nullptr;
  if (lhs->index_end) return nullptr;  // Part-select, not array index.
  auto idx = EvalExpr(lhs->index, ctx, ctx.GetArena());
  auto elem_name =
      std::string(lhs->base->text) + "[" + std::to_string(idx.ToUint64()) + "]";
  return ctx.FindVariable(elem_name);
}

// §7.4: Build a compound name from chained selects (e.g., mem[i][j]).
bool BuildCompoundLhsName(const Expr* expr, SimContext& ctx, Arena& arena,
                          std::string& name) {
  if (expr->kind == ExprKind::kIdentifier) {
    name = expr->text;
    return true;
  }
  if (expr->kind != ExprKind::kSelect || expr->index_end) return false;
  if (!BuildCompoundLhsName(expr->base, ctx, arena, name)) return false;
  auto idx = EvalExpr(expr->index, ctx, arena).ToUint64();
  name += "[" + std::to_string(idx) + "]";
  return true;
}

// §7.4: Multi-dim array element write — create element lazily.
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

// Find the target variable for a compound LHS expression.
Variable* ResolveLhsVariable(const Expr* lhs, SimContext& ctx) {
  if (lhs->kind == ExprKind::kIdentifier) return ctx.FindVariable(lhs->text);
  if (lhs->kind == ExprKind::kMemberAccess) {
    std::string name;
    BuildLhsName(lhs, name);
    return ctx.FindVariable(name);
  }
  if (lhs->kind == ExprKind::kSelect && lhs->base) {
    return ResolveLhsVariable(lhs->base, ctx);
  }
  return nullptr;
}

// §7.2: Write to a packed struct/union field by name.
bool WriteStructField(const Expr* lhs, const Logic4Vec& rhs_val,
                      SimContext& ctx, Arena& arena) {
  std::string name;
  BuildLhsName(lhs, name);
  auto dot = name.find('.');
  if (dot == std::string::npos) return false;
  auto base_name = std::string_view(name).substr(0, dot);
  auto field_name = std::string_view(name).substr(dot + 1);
  // §8.11: 'this' refers to the current instance.
  if (base_name == "this") {
    auto* self = ctx.CurrentThis();
    if (self) {
      self->SetProperty(std::string(field_name), rhs_val);
      return true;
    }
    return false;
  }
  // §8.15: 'super' refers to the base class of the current instance.
  if (base_name == "super") {
    auto* self = ctx.CurrentThis();
    if (self && self->type && self->type->parent) {
      self->SetPropertyForType(std::string(field_name), self->type->parent,
                               rhs_val);
      return true;
    }
    return false;
  }
  // §8.23: Write to a static property via class scope resolution (Class::prop).
  auto* cls_type = ctx.FindClassType(base_name);
  if (cls_type) {
    auto sit = cls_type->static_properties.find(std::string(field_name));
    if (sit != cls_type->static_properties.end()) {
      sit->second = rhs_val;
      return true;
    }
    return false;
  }
  auto* base_var = ctx.FindVariable(base_name);
  if (!base_var) return false;
  auto* info = ctx.GetVariableStructType(base_name);
  if (info) {
    for (const auto& f : info->fields) {
      if (f.name != field_name) continue;
      uint64_t old_val = base_var->value.ToUint64();
      uint64_t mask =
          (f.width >= 64) ? ~uint64_t{0} : (uint64_t{1} << f.width) - 1;
      uint64_t new_bits = (rhs_val.ToUint64() & mask) << f.bit_offset;
      uint64_t cleared = old_val & ~(mask << f.bit_offset);
      base_var->value =
          MakeLogic4VecVal(arena, base_var->value.width, cleared | new_bits);
      base_var->NotifyWatchers();
      return true;
    }
  }
  auto handle = base_var->value.ToUint64();
  auto* obj = ctx.GetClassObject(handle);
  if (obj) {
    // §8.14: Write through the declared type so overridden members are scoped.
    auto declared = ctx.GetVariableClassType(base_name);
    if (!declared.empty()) {
      auto* declared_type = ctx.FindClassType(declared);
      if (declared_type) {
        obj->SetPropertyForType(field_name, declared_type, rhs_val);
        return true;
      }
    }
    obj->SetProperty(std::string(field_name), rhs_val);
    return true;
  }
  return false;
}

// Write a range of bits [hi:lo] into var.
static void WritePartSelect(Variable* var, uint32_t lo, uint32_t width,
                            const Logic4Vec& rhs_val, Arena& arena) {
  uint64_t mask = (width >= 64) ? ~uint64_t{0} : (uint64_t{1} << width) - 1;
  uint64_t old_val = var->value.ToUint64();
  uint64_t new_bits = (rhs_val.ToUint64() & mask) << lo;
  uint64_t cleared = old_val & ~(mask << lo);
  var->value = MakeLogic4VecVal(arena, var->value.width, cleared | new_bits);
}

// Write rhs_val to var at the bit position(s) indicated by a Select LHS.
void WriteBitSelect(Variable* var, const Expr* lhs, const Logic4Vec& rhs_val,
                    SimContext& ctx, Arena& arena) {
  auto idx = static_cast<uint32_t>(EvalExpr(lhs->index, ctx, arena).ToUint64());
  if (!lhs->index_end) {
    uint64_t old_val = var->value.ToUint64();
    uint64_t bit = rhs_val.ToUint64() & 1;
    uint64_t cleared = old_val & ~(uint64_t{1} << idx);
    var->value =
        MakeLogic4VecVal(arena, var->value.width, cleared | (bit << idx));
    return;
  }
  // Part-select: compute (lo, width).
  uint32_t lo = idx;
  auto end_val =
      static_cast<uint32_t>(EvalExpr(lhs->index_end, ctx, arena).ToUint64());
  uint32_t w = end_val;
  if (lhs->is_part_select_plus) {
    // [idx +: w] — lo stays idx.
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
  WritePartSelect(var, lo, w, rhs_val, arena);
}

// §11.8.2: Resize value to target width, sign-extending when signed.
Logic4Vec ResizeToWidth(Logic4Vec val, uint32_t target_width, Arena& arena) {
  if (val.width == target_width || target_width == 0) return val;
  // Check for x/z bits that need preserving.
  bool has_xz = false;
  for (uint32_t i = 0; i < val.nwords && !has_xz; ++i)
    has_xz = val.words[i].bval != 0;
  if (!has_xz) {
    uint64_t v = val.ToUint64();
    if (val.is_signed && target_width > val.width && val.width > 0 &&
        val.width < 64) {
      uint64_t sign_bit = uint64_t{1} << (val.width - 1);
      if (v & sign_bit) v |= ~uint64_t{0} << val.width;
    }
    return MakeLogic4VecVal(arena, target_width, v);
  }
  // Preserve x/z bits during resize.
  auto result = MakeLogic4Vec(arena, target_width);
  result.is_signed = val.is_signed;
  uint32_t copy_words = std::min(val.nwords, result.nwords);
  for (uint32_t i = 0; i < copy_words; ++i) {
    result.words[i].aval = val.words[i].aval;
    result.words[i].bval = val.words[i].bval;
  }
  // Mask off bits beyond target_width in the last word.
  uint32_t last_bit = target_width % 64;
  if (last_bit != 0) {
    uint32_t last_word = (target_width - 1) / 64;
    uint64_t mask = (uint64_t{1} << last_bit) - 1;
    result.words[last_word].aval &= mask;
    result.words[last_word].bval &= mask;
  }
  return result;
}

// §7.6: Copy elements from one array to another (B = A).
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

// §5.11: Find value for array index from named pattern (index/default keys).
static Logic4Vec FindArrayKeyedValue(const Expr* rhs, uint32_t idx,
                                     uint32_t width, SimContext& ctx,
                                     Arena& arena) {
  // Pass 1: explicit index key.
  for (size_t i = 0; i < rhs->pattern_keys.size(); ++i) {
    if (i >= rhs->elements.size()) break;
    auto& key = rhs->pattern_keys[i];
    if (key == "default") continue;
    if (static_cast<uint32_t>(std::stoul(std::string(key))) == idx)
      return EvalExpr(rhs->elements[i], ctx, arena);
  }
  // Pass 2: default key.
  for (size_t i = 0; i < rhs->pattern_keys.size(); ++i) {
    if (i >= rhs->elements.size()) break;
    if (rhs->pattern_keys[i] == "default")
      return EvalExpr(rhs->elements[i], ctx, arena);
  }
  return MakeLogic4VecVal(arena, width, 0);
}

// §7.4: Distribute assignment pattern elements to array element variables.
static void DistributePatternToArray(std::string_view arr_name,
                                     const ArrayInfo& info, const Expr* rhs,
                                     SimContext& ctx, Arena& arena) {
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
      elem->value = ResizeToWidth(
          FindArrayKeyedValue(rhs, idx, info.elem_width, ctx, arena),
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

// §10.10: Collect flattened elements from an unpacked array concatenation.
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
    elems.push_back(EvalExpr(item, ctx, arena));
  }
  return elems;
}

// §10.10: Distribute unpacked array concatenation elements to array variables.
static void DistributeConcatToArray(std::string_view arr_name,
                                    const ArrayInfo& info, const Expr* rhs,
                                    SimContext& ctx, Arena& arena) {
  auto elems = CollectConcatElements(rhs, ctx, arena);
  for (uint32_t i = 0; i < info.size; ++i) {
    uint32_t idx =
        info.is_descending ? (info.lo + info.size - 1 - i) : (info.lo + i);
    auto name = std::string(arr_name) + "[" + std::to_string(idx) + "]";
    auto* elem = ctx.FindVariable(name);
    if (!elem) continue;
    if (i < elems.size()) {
      elem->value = ResizeToWidth(elems[i], info.elem_width, arena);
    } else {
      elem->value = MakeLogic4VecVal(arena, info.elem_width, 0);
    }
    elem->NotifyWatchers();
  }
}

// §7.4/§7.6: Try array-level blocking assignment (pattern, concat, or copy).
bool TryArrayBlockingAssign(const Stmt* stmt, SimContext& ctx, Arena& arena) {
  if (stmt->lhs->kind != ExprKind::kIdentifier) return false;
  if (stmt->rhs && stmt->rhs->kind == ExprKind::kAssignmentPattern) {
    auto* ainfo = ctx.FindArrayInfo(stmt->lhs->text);
    if (ainfo) {
      DistributePatternToArray(stmt->lhs->text, *ainfo, stmt->rhs, ctx, arena);
      return true;
    }
  }
  // §10.10: Unpacked array concatenation assigned to fixed-size array.
  if (stmt->rhs && stmt->rhs->kind == ExprKind::kConcatenation) {
    auto* ainfo = ctx.FindArrayInfo(stmt->lhs->text);
    if (ainfo) {
      DistributeConcatToArray(stmt->lhs->text, *ainfo, stmt->rhs, ctx, arena);
      return true;
    }
  }
  if (stmt->rhs->kind == ExprKind::kIdentifier) {
    auto* dst = ctx.FindArrayInfo(stmt->lhs->text);
    auto* src = ctx.FindArrayInfo(stmt->rhs->text);
    if (dst && src) {
      // §7.6: Copying a dynamic array or queue into a fixed-size array with a
      // different number of elements is a run-time error.
      if (!dst->is_dynamic && !dst->is_queue &&
          (src->is_dynamic || src->is_queue) && dst->size != src->size) {
        ctx.GetDiag().Error(
            {}, "array size mismatch in assignment to fixed-size array");
        return true;
      }
      CopyArrayElements(stmt->lhs->text, *dst, stmt->rhs->text, *src, ctx);
      return true;
    }
  }
  return false;
}

// §7.8: Associative array indexed write (aa[key] = val).
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
    auto key = SignExtend(key_val.ToUint64(), aa->index_width);
    aa->int_data[key] = rhs_val;
  }
  return true;
}

// §7.10.1: Queue indexed write (q[i] = val).
bool TryQueueIndexedWrite(const Expr* lhs, const Logic4Vec& rhs_val,
                          SimContext& ctx, Arena& /*arena*/) {
  if (!lhs->base || lhs->base->kind != ExprKind::kIdentifier) return false;
  auto* q = ctx.FindQueue(lhs->base->text);
  if (!q || !lhs->index) return false;
  auto& arena = ctx.GetArena();
  bool idx_xz = false;
  auto idx = EvalQueueIndex(lhs->index, q, ctx, arena, &idx_xz);
  // §7.10.1: x/z index — ignore write with warning.
  if (idx_xz) {
    ctx.GetDiag().Warning({}, "queue write index contains x/z");
    return true;
  }
  auto sz = static_cast<int64_t>(q->elements.size());
  // §7.10.1: Writing to Q[$+1] is legal — append.
  if (idx == sz) {
    bool has_room =
        (q->max_size < 0) || (static_cast<int32_t>(q->elements.size()) <
                              q->max_size);
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
  // §7.10.1: Invalid index (negative or beyond $+1) — ignore with warning.
  ctx.GetDiag().Warning({}, "queue write index out of bounds");
  return true;
}

// §7.10: Evaluate a queue index expression with $ = last index.
// Sets *has_xz to true if the index contains x/z bits.
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

// §7.10.1: Collect elements from a queue slice (q[lo:hi]).
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
  // §7.10.1: If either bound contains x/z, yield empty queue.
  if (lo_xz || hi_xz) return true;
  // §7.10.1: a < 0 → same as Q[0:b].
  if (lo < 0) lo = 0;
  auto qsz = static_cast<int64_t>(q->elements.size());
  // §7.10.1: b > $ → same as Q[a:$].
  if (hi >= qsz) hi = qsz - 1;
  // §7.10.1: a > b → empty queue (loop simply doesn't execute).
  for (int64_t i = lo; i <= hi; ++i)
    out.push_back(q->elements[static_cast<size_t>(i)]);
  return true;
}

// §7.10: Collect a single queue element (q[i]) with $ support.
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

// §7.10: Collect elements from an expression for queue assignment.
// §7.6: Collect elements from a fixed-size array for cross-type assignment.
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
    // §7.6: Fixed-size array → queue/dynamic array assignment.
    auto* ai = ctx.FindArrayInfo(expr->text);
    if (ai) {
      CollectFixedArrayElements(expr->text, *ai, ctx, out);
      return;
    }
  }
  if (TryCollectLocatorResult(expr, ctx, arena, out)) return;
  out.push_back(EvalExpr(expr, ctx, arena));
}

// §7.5.1: Copy source array into new[size](src) target.
static void CopyNewInit(const Expr* rhs, QueueObject* q,
                        const std::vector<Logic4Vec>& saved, SimContext& ctx) {
  if (rhs->args.size() < 2) return;
  auto* init_expr = rhs->args[1];
  if (!init_expr || init_expr->kind != ExprKind::kIdentifier) return;
  auto* src = ctx.FindQueue(init_expr->text);
  if (!src) return;
  // §7.5.1: Self-reference (d = new[N](d)) — use saved snapshot.
  const auto& src_elems = (src == q) ? saved : src->elements;
  size_t copy_len = std::min(q->elements.size(), src_elems.size());
  for (size_t i = 0; i < copy_len; ++i) q->elements[i] = src_elems[i];
}

// §7.10.4: Queue assignment from concatenation, slice, or literal.
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
    // §7.5.1: Negative size is a runtime error.
    if (sz < 0) {
      ctx.GetDiag().Error({}, "dynamic array new[] size is negative");
      return true;
    }
    // §7.5.1: Snapshot for self-reference (d = new[N](d)).
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
