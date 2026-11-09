#include <algorithm>
#include <charconv>
#include <cstddef>
#include <cstdint>
#include <deque>
#include <optional>
#include <set>
#include <string_view>
#include <utility>
#include <vector>

#include "elaborator/dollar_scope.h"
#include "elaborator/dollar_scope_internal.h"
#include "elaborator/queue_dim.h"
#include "elaborator/std_package.h"
#include "elaborator/type_eval.h"
#include "parser/ast_design.h"
#include "parser/ast_expr.h"
#include "parser/ast_module.h"
#include "parser/ast_type.h"

namespace delta {

enum class QueueShape : uint8_t { kUnknown, kQueue, kNonQueue, kAbsent };

namespace {

struct ValueAt {
  QueueShape known = QueueShape::kUnknown;
  const DataType* type = nullptr;
  const std::vector<Expr*>* dims = nullptr;
  size_t selected = 0;
  const DollarScope* home = nullptr;
  const DollarScope* members = nullptr;
  const Expr* pending = nullptr;
};

}  // namespace

static ValueAt Known(QueueShape shape) { return {shape}; }

static ValueAt MembersValue(const DollarScope* members) {
  ValueAt value;
  value.members = members;
  return value;
}

static bool HasDimsLeft(const ValueAt& value) {
  return value.dims != nullptr && value.selected < value.dims->size();
}

static bool IsAbsent(const ValueAt& value) {
  return value.known == QueueShape::kAbsent;
}

static bool IsAlias(const DataType& type) {
  return type.kind == DataTypeKind::kNamed || type.type_ref_expr != nullptr;
}

static ValueAt Typed(const DollarType& declared, const DollarScope& found_in,
                     ClassQuery& query, int depth) {
  if (declared.type == nullptr) return Known(QueueShape::kUnknown);
  ValueAt value;
  value.type = declared.type;
  value.dims = declared.dims;
  value.home = declared.where != nullptr ? declared.where : &found_in;
  if (declared.package != nullptr)
    value.home = &PackageScope(declared.package, query, depth);
  return value;
}

static ValueAt ExprValue(const Expr* e, const DollarScope& from,
                         ClassQuery& query, int depth);

static ValueAt Pending(const Expr* e, const DollarScope& from) {
  ValueAt value;
  value.pending = e;
  value.home = &from;
  return value;
}

static const DollarScope& StdScope() {
  static const DollarScope kStd = [] {
    DollarScope scope;
    for (const StdPackageEntry& entry : StdPackageContents()) {
      if (entry.kind == StdPackageMemberKind::kClass)
        scope.classes.emplace(entry.name, DollarClass{});
    }
    return scope;
  }();
  return kStd;
}

static const ModuleDecl* DesignNamed(std::string_view name,
                                     const DollarParams& params) {
  for (const std::vector<ModuleDecl*>* decls :
       {&params.unit->modules, &params.unit->interfaces,
        &params.unit->programs}) {
    const auto kDecl = std::ranges::find(*decls, name, &ModuleDecl::name);
    if (kDecl != decls->end()) return *kDecl;
  }
  return nullptr;
}

static ValueAt DesignValue(std::string_view name, const DollarScope* from,
                           ClassQuery& query, int depth) {
  for (const DollarScope* s = from; s != nullptr; s = s->outer) {
    const auto kNested = s->designs.find(name);
    if (kNested != s->designs.end())
      return MembersValue(&DesignScope(kNested->second, *s, query, depth));
  }
  const ModuleDecl* decl = DesignNamed(name, query.params);
  if (decl == nullptr) return Known(QueueShape::kUnknown);
  return MembersValue(
      &DesignScope(decl, UnitScope(query, depth), query, depth));
}

static ValueAt BlockValue(const DollarBlock& block, const DollarScope& found_in,
                          ClassQuery& query, int depth) {
  if (!block.design.empty())
    return DesignValue(block.design, &found_in, query, depth);
  DollarScope& scope = query.built.emplace_back();
  scope.outer = &found_in;
  if (block.items != nullptr)
    NoteItemNamesAt(*block.items, nullptr, query, depth + 1, scope);
  scope.non_queues.insert(block.genvar);
  NoteLocalNames(block.body, scope);
  return MembersValue(&scope);
}

static bool IsDecimal(std::string_view digits) {
  return !digits.empty() && (digits.size() == 1 || digits.front() != '0') &&
         digits.find_first_not_of("0123456789") == std::string_view::npos;
}

static std::optional<QueueShape> NumberedEnumShape(std::string_view name,
                                                   const EnumMember& member) {
  const std::string_view kDigits = name.starts_with(member.name)
                                       ? name.substr(member.name.size())
                                       : std::string_view{};
  if (!IsDecimal(kDigits)) return std::nullopt;
  const Expr* first = member.range_start;
  const Expr* last = member.range_end != nullptr ? member.range_end : first;
  uint64_t n = 0;
  std::from_chars(kDigits.data(), kDigits.data() + kDigits.size(), n);
  const bool kCounted = member.range_end == nullptr;
  const uint64_t kLow = kCounted ? 0 : std::min(first->int_val, last->int_val);
  const uint64_t kHigh =
      kCounted ? first->int_val : std::max(first->int_val, last->int_val) + 1;
  if (n < kLow || n >= kHigh) return std::nullopt;
  return QueueShape::kNonQueue;
}

static ValueAt NumberedEnumValue(std::string_view name, const DollarScope& s) {
  for (const EnumMember* member : s.numbered_enums) {
    const std::optional<QueueShape> kShape = NumberedEnumShape(name, *member);
    if (kShape.has_value()) return Known(*kShape);
  }
  return Known(QueueShape::kAbsent);
}

static ValueAt ValueOfName(std::string_view name, const DollarScope& from,
                           ClassQuery& query, int depth);

static ValueAt Unwrapped(ValueAt value, ClassQuery& query, int depth);

static ValueAt Selected(const ValueAt& from, bool range, ClassQuery& query,
                        int depth);

static bool NamesATypedef(std::string_view name, const DollarScope& from) {
  for (const DollarScope* s = &from; s != nullptr; s = s->outer) {
    if (s->types.count(name) != 0) return true;
  }
  return false;
}

static ValueAt SelectedPastItsDims(const ValueAt& value) {
  const bool kNotAQueue = value.type != nullptr
                              ? !IsAlias(*value.type)
                              : value.known == QueueShape::kNonQueue;
  return Known(kNotAQueue ? QueueShape::kNonQueue : QueueShape::kUnknown);
}

static ValueAt IteratorValue(const DollarIterator& iterator,
                             const DollarScope& found_in, ClassQuery& query,
                             int depth) {
  ValueAt array = Pending(iterator.array, found_in);
  for (size_t k = 0; k < iterator.position; ++k)
    array = Selected(array, false, query, depth);
  array = Unwrapped(array, query, depth);
  if (!HasDimsLeft(array)) return SelectedPastItsDims(array);
  const Expr* dim = (*array.dims)[array.selected];
  if (dim != nullptr && dim->kind == ExprKind::kIdentifier &&
      NamesATypedef(dim->text, *array.home))
    return ValueOfName(dim->text, *array.home, query, depth);
  return Known(QueueShape::kNonQueue);
}

static ValueAt TableValue(std::string_view name, const DollarScope& s,
                          ClassQuery& query, int depth) {
  const auto kTyped = s.typed_vars.find(name);
  if (kTyped != s.typed_vars.end())
    return Typed(kTyped->second, s, query, depth);
  const auto kType = s.types.find(name);
  if (kType != s.types.end()) return Typed(kType->second, s, query, depth);
  if (s.dollar_params.count(name) != 0) return Known(QueueShape::kNonQueue);
  const auto kValue = s.param_values.find(name);
  if (kValue != s.param_values.end()) return Pending(kValue->second, s);
  if (s.non_queues.count(name) != 0 || s.classes.count(name) != 0)
    return Known(QueueShape::kNonQueue);
  if (s.others.count(name) != 0) return Known(QueueShape::kUnknown);
  return Known(QueueShape::kAbsent);
}

static ValueAt ValueDeclaredIn(std::string_view name, const DollarScope& s,
                               ClassQuery& query, int depth,
                               bool through_imports);

static ValueAt ImportedValue(std::string_view name, const DollarScope& s,
                             ClassQuery& query, int depth) {
  for (const DollarImport& import : s.imports) {
    if (!import.name.empty() && import.name != name) continue;
    const ValueAt kValue = ValueDeclaredIn(
        name, PackageScope(import.package, query, depth), query, depth, false);
    if (!IsAbsent(kValue)) return kValue;
  }
  return Known(QueueShape::kAbsent);
}

static ValueAt ValueDeclaredIn(std::string_view name, const DollarScope& s,
                               ClassQuery& query, int depth,
                               bool through_imports) {
  const ValueAt kTable = TableValue(name, s, query, depth);
  if (!IsAbsent(kTable)) return kTable;
  const auto kBlock = s.blocks.find(name);
  if (kBlock != s.blocks.end())
    return BlockValue(kBlock->second, s, query, depth);
  const auto kIterator = s.iterators.find(name);
  if (kIterator != s.iterators.end())
    return IteratorValue(kIterator->second, s, query, depth);
  const ValueAt kEnum = NumberedEnumValue(name, s);
  if (!IsAbsent(kEnum) || !through_imports) return kEnum;
  return ImportedValue(name, s, query, depth);
}

static ValueAt ValueOfName(std::string_view name, const DollarScope& from,
                           ClassQuery& query, int depth) {
  for (const DollarScope* s = &from; s != nullptr; s = s->outer) {
    const ValueAt kValue = ValueDeclaredIn(name, *s, query, depth, true);
    if (!IsAbsent(kValue)) return kValue;
  }
  const ValueAt kStd = TableValue(name, StdScope(), query, depth);
  if (!IsAbsent(kStd)) return kStd;
  if (DesignNamed(name, query.params) != nullptr)
    return DesignValue(name, nullptr, query, depth);
  for (const DollarScope* s = &from; s != nullptr; s = s->outer) {
    if (s->implicit_nets.count(name) != 0) return Known(QueueShape::kNonQueue);
  }
  return Known(QueueShape::kUnknown);
}

static const std::vector<DataType>& NoArgs() {
  static const std::vector<DataType> kNoArgs;
  return kNoArgs;
}

static const std::vector<DataType>& ScopeArgs(const DataType& type) {
  return type.scope_param_assignment_written ? type.type_params : NoArgs();
}

static const DollarScope* OwnClassScope(const FoundClass& found,
                                        const DollarScope& from) {
  for (const DollarScope* s = &from; s != nullptr; s = s->outer) {
    if (s->cls != nullptr && s->cls == found.cls) return s;
  }
  return nullptr;
}

static const DollarScope* ScopeOfTypeName(const DataType& type,
                                          const DollarScope& from,
                                          ClassQuery& query, int depth) {
  if (type.scope_name == "$unit") return &UnitScope(query, depth);
  if (type.scope_name == "std") return &StdScope();
  const DollarScope* package_scope =
      NamedPackageScope(type.scope_name, query, depth);
  if (package_scope != nullptr) return package_scope;
  const std::string_view kOuter = type.outer_scope_names.empty()
                                      ? std::string_view{}
                                      : type.outer_scope_names.back();
  const ClassRef kClass{kOuter, type.scope_name, ScopeArgs(type)};
  const FoundClass kFound = ClassOfRef(kClass, from, query, depth);
  if (!type.scope_param_assignment_written) {
    const DollarScope* own = OwnClassScope(kFound, from);
    if (own != nullptr) return own;
  }
  return MembersOf(kFound, query, depth);
}

static FoundClass ClassOfType(const DataType& type, const DollarScope& from,
                              ClassQuery& query, int depth) {
  const DollarScope* home = type.scope_name.empty()
                                ? &from
                                : ScopeOfTypeName(type, from, query, depth);
  FoundClass found = ClassInChain(type.type_name, home, query, depth);
  const std::vector<DataType>& args =
      type.scope_param_assignment_written ? NoArgs() : type.type_params;
  if (!args.empty()) found.spec = {ArgsOfTypes(args), &from};
  return found;
}

static bool LeadsOn(const ValueAt& value) {
  return value.pending != nullptr ||
         (value.type != nullptr && !HasDimsLeft(value) && IsAlias(*value.type));
}

static bool SteppedOn(ValueAt& value, ClassQuery& query, int& depth) {
  if (value.pending != nullptr) {
    value = ExprValue(value.pending, *value.home, query, depth);
    return true;
  }
  const DataType& type = *value.type;
  if (type.type_ref_expr != nullptr) {
    value = ExprValue(type.type_ref_expr, *value.home, query, depth);
    return true;
  }
  const DollarScope* home = value.home;
  if (!type.scope_name.empty())
    home = ScopeOfTypeName(type, *value.home, query, ++depth);
  if (home == nullptr) {
    value = Known(QueueShape::kUnknown);
    return false;
  }
  const ValueAt kNamed = ValueOfName(type.type_name, *home, query, depth);
  if (kNamed.type == nullptr && kNamed.members == nullptr) {
    value.known = kNamed.known;
    return false;
  }
  value = kNamed;
  return true;
}

static ValueAt Unwrapped(ValueAt value, ClassQuery& query, int depth) {
  std::vector<std::pair<const void*, const DollarScope*>> taken;
  bool going = true;
  while (going && LeadsOn(value)) {
    const void* next_step = value.pending != nullptr
                                ? static_cast<const void*>(value.pending)
                                : value.type;
    going = query.following.emplace(next_step, value.home).second;
    if (going) {
      taken.emplace_back(next_step, value.home);
      going = SteppedOn(value, query, depth);
    } else {
      value = Known(QueueShape::kUnknown);
    }
  }
  for (const auto& step : taken) query.following.erase(step);
  return value;
}

static QueueShape ShapeOfValue(const ValueAt& from, ClassQuery& query,
                               int depth) {
  const ValueAt kValue = Unwrapped(from, query, depth);
  if (kValue.members != nullptr) return QueueShape::kNonQueue;
  if (kValue.type == nullptr) return kValue.known;
  if (HasDimsLeft(kValue)) {
    return IsQueueDim((*kValue.dims)[kValue.selected]) ? QueueShape::kQueue
                                                       : QueueShape::kNonQueue;
  }
  return IsAlias(*kValue.type) ? kValue.known : QueueShape::kNonQueue;
}

static ValueAt Selected(const ValueAt& from, bool range, ClassQuery& query,
                        int depth) {
  if (range) return from;
  ValueAt value = Unwrapped(from, query, depth);
  if (value.members != nullptr) return value;
  if (HasDimsLeft(value)) {
    ++value.selected;
    return value;
  }
  return SelectedPastItsDims(value);
}

static ValueAt MemberIn(const DollarScope& scope, std::string_view name,
                        ClassQuery& query, int depth) {
  return ValueDeclaredIn(name, scope, query, depth, false);
}

static const DataType* StructMemberType(const StructMember& member,
                                        ClassQuery& query) {
  if (member.nested_type != nullptr) return member.nested_type;
  if (!member.scope_name.empty() && !member.type_params.empty()) return nullptr;
  DataType& made = query.made.emplace_back();
  made.kind = member.type_kind;
  made.packed_dim_left = member.packed_dim_left;
  made.type_name = member.type_name;
  made.scope_name = member.scope_name;
  made.type_params = member.type_params;
  return &made;
}

static ValueAt StructMemberValue(const DataType& type, std::string_view name,
                                 const DollarScope& home, ClassQuery& query) {
  const auto kMember =
      std::ranges::find(type.struct_members, name, &StructMember::name);
  if (kMember == type.struct_members.end()) return Known(QueueShape::kUnknown);
  ValueAt value;
  value.type = StructMemberType(*kMember, query);
  value.dims = &kMember->unpacked_dims;
  value.home = &home;
  return value;
}

static ValueAt MemberOf(const ValueAt& from, std::string_view name,
                        ClassQuery& query, int depth) {
  const ValueAt kValue = Unwrapped(from, query, depth);
  if (kValue.members != nullptr)
    return MemberIn(*kValue.members, name, query, depth);
  if (kValue.type == nullptr || HasDimsLeft(kValue))
    return Known(QueueShape::kUnknown);
  const DataType& type = *kValue.type;
  if (type.kind == DataTypeKind::kStruct || type.kind == DataTypeKind::kUnion)
    return StructMemberValue(type, name, *kValue.home, query);
  if (type.kind == DataTypeKind::kVirtualInterface)
    return MemberOf(DesignValue(type.type_name, kValue.home, query, depth),
                    name, query, depth);
  const DollarScope* members = MembersOf(
      ClassOfType(type, *kValue.home, query, depth + 1), query, depth + 1);
  if (members == nullptr) return Known(QueueShape::kUnknown);
  return MemberIn(*members, name, query, depth + 1);
}

static const DollarScope& ClassScopeOf(const DollarScope& from) {
  const DollarScope* s = &from;
  while (s->outer != nullptr && s->cls == nullptr) s = s->outer;
  return *s;
}

static ValueAt IdentifierValue(const Expr* e, const DollarScope& from,
                               ClassQuery& query, int depth) {
  if (e->scope_prefix == "$root")
    return DesignValue(e->text, nullptr, query, depth);
  if (e->scope_prefix == "$unit")
    return MemberIn(UnitScope(query, depth), e->text, query, depth);
  const DollarScope& own = ClassScopeOf(from);
  if (e->text == "this") return MembersValue(&own);
  if (e->text == "super") return MembersValue(own.base);
  if (TypeNameToDataType(e->text).kind != DataTypeKind::kNamed)
    return Known(QueueShape::kNonQueue);
  return ValueOfName(e->text, from, query, depth);
}

static ValueAt ScopedValue(const Expr* e, const DollarScope& from,
                           ClassQuery& query, int depth) {
  const Expr* prefix = e->lhs;
  const DollarScope* named = prefix->kind == ExprKind::kIdentifier
                                 ? NamedPackageScope(prefix->text, query, depth)
                                 : nullptr;
  if (named != nullptr) return MemberIn(*named, e->rhs->text, query, depth);
  const DollarScope* members = MembersOf(
      ClassOfPrefix(prefix, from, query, depth + 1), query, depth + 1);
  if (members == nullptr) return Known(QueueShape::kUnknown);
  return MemberIn(*members, e->rhs->text, query, depth + 1);
}

static ValueAt ExprValue(const Expr* e, const DollarScope& from,
                         ClassQuery& query, int depth) {
  switch (e->kind) {
    case ExprKind::kIdentifier:
      return IdentifierValue(e, from, query, depth);
    case ExprKind::kSelect:
      return Selected(ExprValue(e->base, from, query, depth),
                      e->index_end != nullptr, query, depth);
    case ExprKind::kMemberAccess:
      if (e->is_scope_resolution) return ScopedValue(e, from, query, depth);
      return MemberOf(ExprValue(e->lhs, from, query, depth), e->rhs->text,
                      query, depth);
    case ExprKind::kIntegerLiteral:
    case ExprKind::kRealLiteral:
    case ExprKind::kTimeLiteral:
    case ExprKind::kStringLiteral:
    case ExprKind::kUnbasedUnsizedLiteral:
    case ExprKind::kUnary:
    case ExprKind::kBinary:
    case ExprKind::kConcatenation:
    case ExprKind::kReplicate:
      return Known(QueueShape::kNonQueue);
    default:
      return Known(QueueShape::kUnknown);
  }
}

bool DesignatesNonQueue(const Expr* e, const DollarScope& scope,
                        const DollarParams& params) {
  std::deque<DollarScope> built;
  ClassQuery query{params, built};
  return ShapeOfValue(ExprValue(e, scope, query, 0), query, 0) ==
         QueueShape::kNonQueue;
}

}  // namespace delta
