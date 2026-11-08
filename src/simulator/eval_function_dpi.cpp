#include <algorithm>
#include <cstddef>
#include <cstdint>
#include <cstdlib>
#include <cstring>
#include <string>
#include <string_view>
#include <utility>
#include <vector>

#include "common/arena.h"
#include "common/diagnostic.h"
#include "common/types.h"
#include "parser/ast_expr.h"
#include "parser/ast_type.h"
#include "simulator/dpi_arg_value.h"
#include "simulator/dpi_export.h"
#include "simulator/dpi_runtime.h"
#include "simulator/eval_expr_internal.h"
#include "simulator/eval_function_internal.h"
#include "simulator/evaluation.h"
#include "simulator/instance_prefix_override.h"
#include "simulator/sim_context.h"
#include "simulator/sim_context_types.h"
#include "simulator/statement_assign.h"
#include "simulator/statement_assign_internal.h"
#include "simulator/struct_string_member.h"
#include "simulator/svdpi.h"
#include "simulator/variable.h"

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

uint32_t DpiKindWidth(DataTypeKind kind) {
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

uint32_t DpiValueWidth(DataTypeKind kind, uint32_t declared) {
  uint32_t kind_width = DpiKindWidth(kind);
  return declared > kind_width ? declared : kind_width;
}

bool IsRealKind(DataTypeKind kind) {
  return kind == DataTypeKind::kReal || kind == DataTypeKind::kShortreal ||
         kind == DataTypeKind::kRealtime;
}

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

SvChandle ChandleOfWord(Logic4Word w) {
  SvChandle handle = nullptr;
  auto bits = static_cast<uintptr_t>(w.aval);
  std::memcpy(static_cast<void*>(&handle), &bits, sizeof(handle));
  return handle;
}

std::vector<SvLogicVecVal> CanonicalWordsOfVec(const Logic4Vec& v,
                                               uint32_t width) {
  std::vector<SvLogicVecVal> words(DpiCanonicalWordCount(width),
                                   SvLogicVecVal{0, 0});
  for (size_t i = 0; i < words.size(); ++i) {
    size_t src = i / 2;
    if (src >= v.nwords) break;
    unsigned shift = (i % 2) == 0 ? 0U : 32U;
    words[i].aval = static_cast<uint32_t>(v.words[src].aval >> shift);
    words[i].bval = static_cast<uint32_t>(v.words[src].bval >> shift);
  }
  if (uint32_t rem = width % 32U; rem != 0 && !words.empty()) {
    uint32_t mask = (1U << rem) - 1U;
    words.back().aval &= mask;
    words.back().bval &= mask;
  }
  return words;
}

Logic4Vec VecOfCanonicalWords(Arena& arena,
                              const std::vector<SvLogicVecVal>& words,
                              uint32_t width) {
  Logic4Vec v = MakeLogic4Vec(arena, width);
  for (size_t i = 0; i < words.size(); ++i) {
    size_t dst = i / 2;
    if (dst >= v.nwords) break;
    unsigned shift = (i % 2) == 0 ? 0U : 32U;
    v.words[dst].aval |= static_cast<uint64_t>(words[i].aval) << shift;
    v.words[dst].bval |= static_cast<uint64_t>(words[i].bval) << shift;
  }
  return v;
}

DpiArgValue DpiArgValueOfType(DataTypeKind kind, uint32_t declared_width,
                              const Logic4Vec& v) {
  if (uint32_t width = DpiValueWidth(kind, declared_width);
      width > DpiInlineValueBits(kind)) {
    return DpiArgValue::FromLogicVecWords(CanonicalWordsOfVec(v, width), width,
                                          kind);
  }
  Logic4Word word = v.nwords == 0 ? Logic4Word{} : v.words[0];
  Logic4Word known{word.aval & ~word.bval, 0};
  DpiArgValue out;
  switch (kind) {
    case DataTypeKind::kReal:
    case DataTypeKind::kShortreal:
    case DataTypeKind::kRealtime:
      out = DpiArgValue::FromReal(v.is_real ? RealVecToDouble(v)
                                            : static_cast<double>(known.aval));
      out.type = kind;
      return out;
    case DataTypeKind::kChandle:
      return DpiArgValue::FromChandle(ChandleOfWord(known));
    case DataTypeKind::kBit:
      return DpiArgValue::FromBit(static_cast<SvBit>(known.aval & 1U));
    case DataTypeKind::kLogic:
    case DataTypeKind::kReg:
      out = DpiArgValue::FromLogic(SvLogicOfWord(word));
      out.type = kind;
      return out;
    case DataTypeKind::kInteger:
      return DpiArgValue::FromLogicVec(SvLogicVecVal{
          static_cast<uint32_t>(word.aval), static_cast<uint32_t>(word.bval)});
    case DataTypeKind::kTime:
      return DpiArgValue::FromLogicVecWords(CanonicalWordsOfVec(v, 64), 64,
                                            kind);
    case DataTypeKind::kString:
      return DpiArgValue::FromString(Logic4VecToString(v));
    default:
      return CoerceArgValue(
          DpiArgValue::FromLongint(static_cast<int64_t>(known.aval)), kind);
  }
}

Logic4Vec DpiValueOfType(Arena& arena, DataTypeKind kind,
                         uint32_t declared_width, const DpiArgValue& value,
                         bool is_signed) {
  if (value.IsWideVec()) {
    Logic4Vec wide =
        VecOfCanonicalWords(arena, value.AsLogicVecWords(), value.VecWidth());
    wide.is_signed = is_signed;
    return wide;
  }
  uint32_t width = DpiValueWidth(kind, declared_width);
  if (IsRealKind(kind)) return MakeRealVec(arena, value.AsReal(), width);
  if (kind == DataTypeKind::kString) {
    return StringToLogic4Vec(arena, value.AsString());
  }

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
  v.is_signed = is_signed;
  return v;
}

struct UnpackedActual {
  std::vector<Variable*> elements;
  std::vector<std::string> names;
  std::vector<DpiArrayRange> ranges;
};

std::vector<DpiArrayRange> DeclaredRanges(const ArrayInfo& info) {
  std::vector<DpiArrayRange> ranges;
  const bool kSingle = info.dim_sizes.empty();
  const size_t kCount = kSingle ? 1 : info.dim_sizes.size();
  for (size_t d = 0; d < kCount; ++d) {
    const auto kLow = static_cast<int32_t>(kSingle ? info.lo : info.dim_los[d]);
    const auto kSize =
        static_cast<int32_t>(kSingle ? info.size : info.dim_sizes[d]);
    const bool kDescending =
        kSingle ? info.is_descending
                : d < info.dim_descending.size() && info.dim_descending[d];
    const int32_t kHigh = kLow + kSize - 1;
    ranges.push_back(kDescending ? DpiArrayRange{kHigh, kLow}
                                 : DpiArrayRange{kLow, kHigh});
  }
  return ranges;
}

UnpackedActual UnpackedActualOf(std::string_view name, bool from_left,
                                SimContext& ctx) {
  UnpackedActual actual;
  const ArrayInfo* info = ctx.FindArrayInfo(name);
  if (info == nullptr || info->is_dynamic || info->is_queue) return actual;
  actual.ranges = DeclaredRanges(*info);
  std::vector<std::string> names = {std::string(name)};
  for (const DpiArrayRange& range : actual.ranges) {
    const int32_t kFirst =
        from_left ? range.left : std::min(range.left, range.right);
    const int32_t kStep = from_left && range.left > range.right ? -1 : 1;
    const int32_t kCount = std::abs(range.left - range.right) + 1;
    std::vector<std::string> next;
    for (const std::string& prefix : names) {
      for (int32_t j = 0; j < kCount; ++j) {
        next.push_back(
            prefix + "[" +
            std::to_string(static_cast<uint32_t>(kFirst + (j * kStep))) + "]");
      }
    }
    names = std::move(next);
  }
  for (const std::string& element : names) {
    actual.elements.push_back(ctx.FindVariable(element));
  }
  actual.names = std::move(names);
  return actual;
}

uint32_t MemberElementSlot(const StructFieldInfo& field, uint32_t k) {
  const int64_t kLower = std::min(field.elem_left, field.elem_right);
  const int64_t kFromLeft = std::abs(kLower + k - field.elem_left);
  return field.elem_count - 1 - static_cast<uint32_t>(kFromLeft);
}

uint32_t MemberElementWidth(const StructFieldInfo& field) {
  return field.elem_count == 0 ? field.width : field.width / field.elem_count;
}

DpiArgValue AggregateValue(const DpiArg& formal, const StructTypeInfo& info,
                           const Logic4Vec& bits, Arena& arena) {
  DpiArgValue whole;
  whole.type = formal.type;
  for (size_t m = 0; m < formal.members.size() && m < info.fields.size(); ++m) {
    const DpiArg& member = formal.members[m];
    const StructFieldInfo& field = info.fields[m];
    Logic4Vec held =
        ExtractBitField(arena, bits, field.bit_offset, field.width);
    if (!member.members.empty() && field.nested != nullptr) {
      whole.elements.push_back(
          AggregateValue(member, *field.nested, held, arena));
      continue;
    }
    if (member.unpacked_dims.empty() || field.elem_count == 0) {
      whole.elements.push_back(
          DpiArgValueOfType(member.type, member.width,
                            MemberValueOf(held, field.type_kind, arena)));
      continue;
    }
    DpiArgValue array;
    array.type = member.type;
    const uint32_t kWidth = MemberElementWidth(field);
    for (uint32_t k = 0; k < field.elem_count; ++k) {
      array.elements.push_back(DpiArgValueOfType(
          member.type, member.width,
          ExtractBitField(arena, held, MemberElementSlot(field, k) * kWidth,
                          kWidth)));
    }
    whole.elements.push_back(std::move(array));
  }
  return whole;
}

Logic4Vec MemberBits(const DpiArg& formal, const DpiArgValue& value,
                     DataTypeKind held_kind, uint32_t width, Arena& arena) {
  Logic4Vec next = DpiValueOfType(arena, formal.type, formal.width, value,
                                  !formal.is_unsigned);
  return ResizeToWidth(MemberBitsOf(next, held_kind, arena), width, arena);
}

void DepositAggregate(Logic4Vec& bits, const DpiArg& formal,
                      const StructTypeInfo& info, const DpiArgValue& value,
                      Arena& arena) {
  for (size_t m = 0; m < formal.members.size() && m < info.fields.size() &&
                     m < value.elements.size();
       ++m) {
    const DpiArg& member = formal.members[m];
    const StructFieldInfo& field = info.fields[m];
    const DpiArgValue& part = value.elements[m];
    if (!member.members.empty() && field.nested != nullptr) {
      Logic4Vec held = OwnRhsWords(
          ExtractBitField(arena, bits, field.bit_offset, field.width), arena);
      DepositAggregate(held, member, *field.nested, part, arena);
      DepositBitField(bits, field.bit_offset, held, field.width);
    } else if (member.unpacked_dims.empty() || field.elem_count == 0) {
      DepositBitField(
          bits, field.bit_offset,
          MemberBits(member, part, field.type_kind, field.width, arena),
          field.width);
    } else {
      const uint32_t kWidth = MemberElementWidth(field);
      for (uint32_t k = 0; k < field.elem_count && k < part.elements.size();
           ++k) {
        DepositBitField(
            bits, field.bit_offset + (MemberElementSlot(field, k) * kWidth),
            MemberBits(member, part.elements[k], field.type_kind, kWidth,
                       arena),
            kWidth);
      }
    }
  }
}

DpiArgValue DpiAggregateActual(const DpiArg& formal, const Expr* actual,
                               const ActualBindingCtx& b) {
  DpiArgValue whole;
  whole.type = formal.type;
  if (actual->kind != ExprKind::kIdentifier) return whole;
  const Variable* var = b.ctx.FindVariable(actual->text);
  const StructTypeInfo* info = StructLayoutOfName(actual->text, b.ctx);
  if (var == nullptr || info == nullptr) return whole;
  return AggregateValue(formal, *info, var->value, b.arena);
}

DpiArgValue DpiArrayActual(const DpiArg& formal, const Expr* actual,
                           const ActualBindingCtx& b) {
  DpiArgValue array;
  array.type = formal.type;
  if (actual->kind != ExprKind::kIdentifier) return array;
  UnpackedActual found =
      UnpackedActualOf(actual->text, formal.is_open_array, b.ctx);
  array.ranges = std::move(found.ranges);
  for (size_t k = 0; k < found.elements.size(); ++k) {
    Variable* element = found.elements[k];
    const StructTypeInfo* info =
        formal.members.empty() ? nullptr
                               : StructLayoutOfName(found.names[k], b.ctx);
    if (element == nullptr) {
      array.elements.emplace_back();
    } else if (info != nullptr) {
      array.elements.push_back(
          AggregateValue(formal, *info, element->value, b.arena));
    } else {
      array.elements.push_back(
          DpiArgValueOfType(formal.type, formal.width, element->value));
    }
  }
  return array;
}

DpiArgValue EvalDpiActualForFormal(const DpiRtFunction* import, size_t i,
                                   const ActualBindingCtx& b) {
  DataTypeKind type = import->args[i].type;
  uint32_t width = import->args[i].width;
  int ai = ResolveDpiActualIndex(import, b.call, i, b.positional_count);
  if (ai >= 0 && b.call->args[static_cast<size_t>(ai)] != nullptr &&
      (!import->args[i].unpacked_dims.empty() ||
       import->args[i].is_open_array)) {
    return DpiArrayActual(import->args[i],
                          b.call->args[static_cast<size_t>(ai)], b);
  }
  if (ai >= 0 && b.call->args[static_cast<size_t>(ai)] != nullptr &&
      !import->args[i].members.empty()) {
    return DpiAggregateActual(import->args[i],
                              b.call->args[static_cast<size_t>(ai)], b);
  }
  if (ai >= 0 && b.call->args[static_cast<size_t>(ai)] != nullptr) {
    return DpiArgValueOfType(
        type, width,
        EvalExpr(b.call->args[static_cast<size_t>(ai)], b.ctx, b.arena));
  }
  if (import->args[i].default_value) {
    return DpiArgValueOfType(
        type, width, EvalExpr(import->args[i].default_value, b.ctx, b.arena));
  }
  return DpiRuntime::UndeterminedOutputValue(type, width);
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
    args.push_back(DpiArgValueOfType(DataTypeKind::kInt, 0,
                                     EvalExpr(arg, b.ctx, b.arena)));
  }
  return args;
}

std::vector<DpiArgValue> BindDpiCallActuals(const DpiRtFunction* import,
                                            const ActualBindingCtx& b) {
  if (!import->args.empty()) return BindDpiActualsFromImport(import, b);
  return BindDpiActualsPositional(b);
}

bool AssignmentWouldChangeActual(const Expr* lhs, const Logic4Vec& next,
                                 SimContext& ctx, Arena& arena) {
  Variable* var = lhs != nullptr && lhs->kind == ExprKind::kIdentifier
                      ? ResolveLhsVariable(lhs, ctx)
                      : nullptr;
  if (var == nullptr) return true;
  Logic4Vec stored = ConvertRealOnAssign(next, lhs, *var, ctx, arena);
  if (!var->is_4state) CoerceTo2State(stored);
  return !var->value.SameValueAs(stored);
}

void WritebackDpiArray(const DpiArg& formal, const Expr* lhs,
                       const DpiArgValue& array, const ActualBindingCtx& b) {
  if (lhs->kind != ExprKind::kIdentifier) return;
  UnpackedActual found =
      UnpackedActualOf(lhs->text, formal.is_open_array, b.ctx);
  for (size_t k = 0; k < found.elements.size() && k < array.elements.size();
       ++k) {
    Variable* element = found.elements[k];
    if (element == nullptr) continue;
    const StructTypeInfo* info =
        formal.members.empty() ? nullptr
                               : StructLayoutOfName(found.names[k], b.ctx);
    Logic4Vec next = OwnRhsWords(element->value, b.arena);
    if (info != nullptr) {
      DepositAggregate(next, formal, *info, array.elements[k], b.arena);
    } else {
      next = OwnRhsWords(
          ResizeToWidth(DpiValueOfType(b.arena, formal.type, formal.width,
                                       array.elements[k], !formal.is_unsigned),
                        element->value.width, b.arena),
          b.arena);
    }
    element->value = next;
    element->NotifyWatchers();
  }
}

void WritebackDpiAggregate(const DpiArg& formal, const Expr* lhs,
                           const DpiArgValue& value,
                           const ActualBindingCtx& b) {
  if (lhs->kind != ExprKind::kIdentifier) return;
  Variable* var = b.ctx.FindVariable(lhs->text);
  const StructTypeInfo* info = StructLayoutOfName(lhs->text, b.ctx);
  if (var == nullptr || info == nullptr) return;
  Logic4Vec next = OwnRhsWords(var->value, b.arena);
  DepositAggregate(next, formal, *info, value, b.arena);
  var->value = next;
  var->NotifyWatchers();
}

void WritebackDpiChangedArgs(const DpiRtFunction* import,
                             const ActualBindingCtx& b,
                             const std::vector<DpiArgValue>& actuals,
                             const std::vector<DpiArgValueChange>& changes) {
  for (const auto& change : changes) {
    size_t i = change.index;
    if (i >= import->args.size() || i >= actuals.size()) continue;
    int ai = ResolveDpiActualIndex(import, b.call, i, b.positional_count);
    if (ai < 0) continue;
    const Expr* lhs = b.call->args[static_cast<size_t>(ai)];
    if (!import->args[i].unpacked_dims.empty() ||
        import->args[i].is_open_array) {
      WritebackDpiArray(import->args[i], lhs, actuals[i], b);
      continue;
    }
    if (!import->args[i].members.empty()) {
      WritebackDpiAggregate(import->args[i], lhs, actuals[i], b);
      continue;
    }
    Logic4Vec next =
        DpiValueOfType(b.arena, import->args[i].type, import->args[i].width,
                       actuals[i], !import->args[i].is_unsigned);
    if (!AssignmentWouldChangeActual(lhs, next, b.ctx, b.arena)) continue;
    PerformBlockingAssign(lhs, next, b.ctx, b.arena);
  }
}

std::string ExportTempName(std::string_view key, size_t index) {
  std::string name = "$dpi_export$" + std::string(key);
  std::replace(name.begin(), name.end(), '.', '$');
  return name + "$" + std::to_string(index);
}

void EnsureExportTemp(const std::string& name, const DpiArg& formal,
                      SimContext& ctx) {
  Arena& arena = ctx.GetArena();
  auto kept = [&arena](const std::string& text) -> std::string_view {
    return *arena.Create<std::string>(text);
  };
  if (formal.unpacked_dims.empty() ? ctx.FindVariable(name) != nullptr
                                   : ctx.FindArrayInfo(name) != nullptr) {
    return;
  }
  const StructTypeInfo* layout =
      formal.members.empty()
          ? nullptr
          : ctx.FindStructType(FormalLayoutKey(*formal.declaration, ctx));
  const uint32_t kWidth = layout != nullptr
                              ? layout->total_width
                              : DpiValueWidth(formal.type, formal.width);
  const std::string_view kName = kept(name);
  if (layout != nullptr) ctx.SetVariableStructType(kName, layout->type_name);
  if (formal.unpacked_dims.empty()) {
    ctx.CreateVariable(kName, kWidth)->is_string =
        formal.type == DataTypeKind::kString;
    return;
  }
  ArrayInfo info;
  info.lo = static_cast<uint32_t>(formal.unpacked_dims.front().low);
  info.size = static_cast<uint32_t>(formal.unpacked_dims.front().high -
                                    formal.unpacked_dims.front().low + 1);
  info.elem_width = kWidth;
  info.elem_type_kind = formal.type;
  if (formal.unpacked_dims.size() > 1) {
    for (const SvActualDimension& dim : formal.unpacked_dims) {
      info.dim_los.push_back(static_cast<uint32_t>(dim.low));
      info.dim_sizes.push_back(static_cast<uint32_t>(dim.high - dim.low + 1));
      info.dim_descending.push_back(false);
    }
  }
  ctx.RegisterArray(kName, info);
  for (const std::string& element : UnpackedActualOf(name, false, ctx).names) {
    ctx.CreateVariable(kept(element), kWidth);
  }
}

Expr* IdentifierNaming(const std::string& text, Arena& arena) {
  auto* id = arena.Create<Expr>();
  id->kind = ExprKind::kIdentifier;
  id->text = *arena.Create<std::string>(text);
  return id;
}

void SendExportArguments(std::string_view key,
                         const std::vector<DpiArg>& formals,
                         const std::vector<DpiArgValue>& args, Expr* call,
                         const ActualBindingCtx& b) {
  for (size_t i = 0; i < formals.size() && i < args.size(); ++i) {
    const DpiArg& formal = formals[i];
    const std::string kTemp = ExportTempName(key, i);
    EnsureExportTemp(kTemp, formal, b.ctx);
    Expr* actual = IdentifierNaming(kTemp, b.arena);
    call->args.push_back(actual);
    if (formal.direction == Direction::kOutput) continue;
    if (!formal.unpacked_dims.empty()) {
      WritebackDpiArray(formal, actual, args[i], b);
      continue;
    }
    if (!formal.members.empty()) {
      WritebackDpiAggregate(formal, actual, args[i], b);
      continue;
    }
    PerformBlockingAssign(actual,
                          DpiValueOfType(b.arena, formal.type, formal.width,
                                         args[i], !formal.is_unsigned),
                          b.ctx, b.arena);
  }
}

void ReceiveExportArguments(const std::vector<DpiArg>& formals,
                            std::vector<DpiArgValue>& args,
                            const ActualBindingCtx& b) {
  for (size_t i = 0; i < formals.size() && i < args.size(); ++i) {
    const DpiArg& formal = formals[i];
    if (formal.direction == Direction::kInput) continue;
    const Expr* actual = b.call->args[i];
    args[i] = !formal.unpacked_dims.empty() ? DpiArrayActual(formal, actual, b)
              : !formal.members.empty()
                  ? DpiAggregateActual(formal, actual, b)
                  : DpiArgValueOfType(formal.type, formal.width,
                                      EvalExpr(actual, b.ctx, b.arena));
  }
}

}  // namespace

static std::string_view DpiCalleeName(const Expr* expr) {
  if (!expr->callee.empty()) return expr->callee;
  const Expr* scoped = expr->lhs;
  if (scoped == nullptr || scoped->kind != ExprKind::kMemberAccess ||
      !scoped->is_scope_resolution || scoped->rhs == nullptr ||
      scoped->rhs->kind != ExprKind::kIdentifier) {
    return {};
  }
  return scoped->rhs->text;
}

bool BeginDpiImportCall(const Expr* expr, SimContext& ctx, Arena& arena,
                        DpiImportCall& call) {
  call.dpi = ctx.GetDpiRuntime();
  call.expr = expr;
  call.callee = DpiCalleeName(expr);
  call.import = call.dpi == nullptr ? nullptr
                                    : call.dpi->FindImportIn(
                                          ctx.ActiveUnitScope(), call.callee);
  if (call.import == nullptr) return false;
  if (!call.import->impl && !call.import->arg_impl) {
    std::string message = "imported subroutine '" + std::string(call.callee) +
                          "' is bound to no foreign implementation";
    if (!call.import->unbound_reason.empty()) {
      message += ": " + call.import->unbound_reason;
    }
    ctx.GetDiag().Error(expr->range.start, std::move(message),
                        Subclause("35.5.4"));
    return false;
  }
  ActualBindingCtx binding{expr, expr->args.size() - expr->arg_names.size(),
                           ctx, arena};
  call.args = BindDpiCallActuals(call.import, binding);

  DpiScope scope;
  scope.name = DpiInstanceScopeName(ctx.ActiveInstancePrefix(), ctx);
  call.dpi->EnterDeclaredImportCall(call.import->sv_name, std::move(scope));
  return true;
}

void CallDpiImport(DpiImportCall& call) {
  if (call.import->is_pure) {
    call.result =
        call.dpi->CallImportReusingPureResult(call.import->sv_name, call.args);
  } else {
    call.result = call.dpi->CallImportDetectingChanges(call.import->sv_name,
                                                       call.args, call.changes);
  }
}

Logic4Vec FinishDpiImportCall(DpiImportCall& call, SimContext& ctx,
                              Arena& arena) {
  if (!call.import->is_pure) {
    ActualBindingCtx binding{
        call.expr, call.expr->args.size() - call.expr->arg_names.size(), ctx,
        arena};
    WritebackDpiChangedArgs(call.import, binding, call.args, call.changes);
  }

  call.dpi->LeaveImportCall();

  return DpiValueOfType(arena, call.import->return_type, 0,
                        CoerceArgValue(call.result, call.import->return_type),
                        !call.import->return_is_unsigned);
}

Logic4Vec EvalDpiCall(const Expr* expr, SimContext& ctx, Arena& arena) {
  DpiImportCall call;
  if (!BeginDpiImportCall(expr, ctx, arena, call)) {
    return MakeLogic4VecVal(arena, 1, 0);
  }
  CallDpiImport(call);
  return FinishDpiImportCall(call, ctx, arena);
}

Expr* DpiExportCall(std::string_view key, const DpiRtExport& exp,
                    const std::vector<DpiArgValue>& args, SimContext& ctx) {
  Arena& arena = ctx.GetArena();
  auto* call = arena.Create<Expr>();
  call->kind = ExprKind::kCall;
  call->callee = *arena.Create<std::string>(key);
  ActualBindingCtx binding{call, exp.args.size(), ctx, arena};
  SendExportArguments(key, exp.args, args, call, binding);
  return call;
}

void ReadDpiExportOutputs(const Expr* call, const DpiRtExport& exp,
                          std::vector<DpiArgValue>& args, SimContext& ctx) {
  ActualBindingCtx binding{call, exp.args.size(), ctx, ctx.GetArena()};
  ReceiveExportArguments(exp.args, args, binding);
}

DpiArgValue CallDpiExportedFunction(std::string_view key,
                                    const DpiRtExport& exp,
                                    std::vector<DpiArgValue>& args,
                                    SimContext& ctx) {
  Expr* call = DpiExportCall(key, exp, args, ctx);
  InstancePrefixOverride root(ctx.InstancePrefixOverride(), "");
  Logic4Vec value = EvalExpr(call, ctx, ctx.GetArena());
  ReadDpiExportOutputs(call, exp, args, ctx);
  return DpiArgValueOfType(exp.return_type, 0, value);
}

}  // namespace delta
