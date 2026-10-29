#include "elaborator/expression_self_type.h"

#include <algorithm>
#include <array>
#include <cstddef>
#include <cstdint>
#include <cstdlib>
#include <optional>
#include <span>
#include <string>
#include <string_view>
#include <utility>
#include <vector>

#include "common/arena.h"
#include "elaborator/aggregate_shape.h"
#include "elaborator/const_eval.h"
#include "elaborator/const_eval_internal.h"
#include "elaborator/operator_classes.h"
#include "elaborator/system_function_types.h"
#include "elaborator/type_eval.h"
#include "elaborator/typename_writer.h"
#include "elaborator/unpacked_array_type.h"
#include "lexer/token.h"
#include "parser/ast_expr.h"
#include "parser/ast_type.h"
#include "parser/parser_token_skips.h"

namespace delta {
namespace {

// The self-determined width, signing and state of an operand, or for a real
// operand the real kind it is, kImplicit for any other.
struct Shape {
  uint32_t width = 0;
  bool is_signed = false;
  bool four_state = false;
  DataTypeKind real_kind = DataTypeKind::kImplicit;
};

// How many typedef names a select follows to the packed dimensions a type is
// written with before a cyclic chain is given up on.
constexpr int kMaxNameHops = 16;

bool IsReal(const Shape& shape) {
  return shape.real_kind != DataTypeKind::kImplicit;
}

Shape OneBit(bool four_state) { return {1, false, four_state}; }

// §11.3.1: real where either operand is, else shortreal where either is.
DataTypeKind RealOfEither(const Shape& a, const Shape& b) {
  if (a.real_kind == DataTypeKind::kReal || b.real_kind == DataTypeKind::kReal)
    return DataTypeKind::kReal;
  if (IsReal(a) || IsReal(b)) return DataTypeKind::kShortreal;
  return DataTypeKind::kImplicit;
}

// §11.6.1 with §11.8.1: as wide as the wider operand, signed where both are,
// 4-state where either is.
Shape Widest(const Shape& a, const Shape& b) {
  return {std::max(a.width, b.width), a.is_signed && b.is_signed,
          a.four_state || b.four_state, RealOfEither(a, b)};
}

// §11.6.1: a shift or a power is its left operand's width and signing.
Shape LeftSized(const Shape& left, const Shape& right) {
  return {left.width, left.is_signed, left.four_state || right.four_state,
          RealOfEither(left, right)};
}

Expr* IntLiteral(Arena& arena, uint32_t value) {
  auto* literal = arena.Create<Expr>();
  literal->kind = ExprKind::kIntegerLiteral;
  literal->int_val = value;
  return literal;
}

DataType TypeOfShape(const Shape& shape, Arena& arena) {
  if (shape.real_kind == DataTypeKind::kShortreal)
    return TypeNameToDataType("shortreal");
  if (IsReal(shape)) return TypeNameToDataType("real");
  return VectorType(shape.width, shape.is_signed, shape.four_state, arena);
}

// The shape of a value of `type`; nothing for a type that is neither
// integral nor real, an unpacked structure, a string or a class among them.
std::optional<Shape> ShapeOf(const DataType& type, const ExprTypeScope& scope) {
  DataTypeKind kind = ResolvedTypeKind(type, scope.typedefs);
  if (kind == DataTypeKind::kShortreal) return Shape{0, true, false, kind};
  if (kind == DataTypeKind::kReal || kind == DataTypeKind::kRealtime)
    return Shape{0, true, false, DataTypeKind::kReal};
  const DataType* end = TypeAtChainEnd(type, scope.typedefs);
  if (end == nullptr) return std::nullopt;
  bool packed_aggregate =
      (kind == DataTypeKind::kStruct || kind == DataTypeKind::kUnion) &&
      end->is_packed;
  if (!IsIntegralType(kind) && !packed_aggregate) return std::nullopt;
  uint32_t width = EvalTypeWidth(type, scope.typedefs, scope.constants);
  if (width == 0) return std::nullopt;
  return Shape{width, IsSignedType(type, scope.typedefs),
               Is4stateType(type, scope.typedefs)};
}

std::optional<Shape> OperandShape(const Expr* expr,
                                  const ExprTypeScope& scope) {
  std::optional<DataType> type = ExprSelfType(expr, scope);
  if (!type) return std::nullopt;
  return ShapeOf(*type, scope);
}

std::optional<DeclaredValue> AsValue(std::optional<DataType> type) {
  if (!type) return std::nullopt;
  return DeclaredValue{std::move(*type), 0};
}

std::optional<DeclaredValue> ValueOf(const Expr* expr,
                                     const ExprTypeScope& scope);

// The number of elements a part-select names: the count its `+:` or `-:`
// writes, or the span between the bounds of `[left:right]`.
std::optional<uint32_t> SelectedCount(const Expr* select,
                                      const ScopeMap& constants) {
  if (select->is_part_select_plus || select->is_part_select_minus) {
    std::optional<int64_t> count = ConstEvalInt(select->index_end, constants);
    if (!count || *count <= 0) return std::nullopt;
    return static_cast<uint32_t>(*count);
  }
  std::optional<int64_t> left = ConstEvalInt(select->index, constants);
  std::optional<int64_t> right = ConstEvalInt(select->index_end, constants);
  if (!left || !right) return std::nullopt;
  return static_cast<uint32_t>(std::abs(*left - *right) + 1);
}

// The type that writes the packed dimensions a select of a value of `type`
// addresses: `type` itself, or the type a typedef name it is written with
// stands for. Null where none writes one, as for an integer atom type, a
// scalar, a structure and an enumeration, whose dimension is its base's.
const DataType* PackedArrayType(const DataType& type,
                                const TypedefMap& typedefs) {
  const DataType* at = &type;
  for (int hops = 0; at != nullptr && hops < kMaxNameHops; ++hops) {
    if (at->kind == DataTypeKind::kEnum) return nullptr;
    if (at->packed_dim_left != nullptr) return at;
    if (at->kind != DataTypeKind::kNamed) return nullptr;
    at = FindNamedType(*at, typedefs);
  }
  return nullptr;
}

// §7.4.1: the element of the packed array `array`, its outermost dimension
// gone. An element of a bit, logic or reg array is unsigned whatever the
// array's signing; one of a named type keeps the type's.
DataType PackedElement(const DataType& array) {
  DataType element = array;
  element.packed_dim_left = nullptr;
  element.packed_dim_right = nullptr;
  if (!element.extra_packed_dims.empty()) {
    element.packed_dim_left = element.extra_packed_dims.front().first;
    element.packed_dim_right = element.extra_packed_dims.front().second;
    element.extra_packed_dims.erase(element.extra_packed_dims.begin());
  }
  if (element.kind == DataTypeKind::kBit ||
      element.kind == DataTypeKind::kLogic ||
      element.kind == DataTypeKind::kReg) {
    element.is_signed = false;
  }
  return element;
}

// §11.5.1: a part-select of a packed array, as many of its elements as it
// names, an unsigned vector of their bits.
std::optional<DataType> PackedPart(const DataType& array, const Expr* select,
                                   const ExprTypeScope& scope) {
  std::optional<uint32_t> count = SelectedCount(select, scope.constants);
  std::optional<Shape> element = ShapeOf(PackedElement(array), scope);
  if (!count || !element) return std::nullopt;
  return TypeOfShape({*count * element->width, false, element->four_state},
                     scope.arena);
}

// §11.5.1: a select of an integral value written with no packed dimension of
// its own -- an integer atom, a scalar, a structure or an enumeration --
// which addresses its bits.
std::optional<DataType> SelectedBits(const DataType& type, const Expr* select,
                                     const ExprTypeScope& scope) {
  std::optional<Shape> whole = ShapeOf(type, scope);
  if (!whole || IsReal(*whole)) return std::nullopt;
  if (select->index_end == nullptr)
    return TypeOfShape(OneBit(whole->four_state), scope.arena);
  std::optional<uint32_t> count = SelectedCount(select, scope.constants);
  if (!count) return std::nullopt;
  return TypeOfShape({*count, false, whole->four_state}, scope.arena);
}

std::optional<DataType> PackedSelectType(const DataType& type,
                                         const Expr* select,
                                         const ExprTypeScope& scope) {
  if (ResolvedTypeKind(type, scope.typedefs) == DataTypeKind::kString) {
    if (select->index_end != nullptr) return std::nullopt;
    return TypeNameToDataType("byte");
  }
  const DataType* array = PackedArrayType(type, scope.typedefs);
  if (array == nullptr) return SelectedBits(type, select, scope);
  if (select->index_end == nullptr) return PackedElement(*array);
  return PackedPart(*array, select, scope);
}

// The value of `type` under the unpacked dimensions `dims`, whose outermost
// makes the kind of array it is.
DeclaredValue UnderDims(DataType type, const std::vector<Expr*>& dims,
                        const ExprTypeScope& scope) {
  DeclaredValue value{std::move(type), static_cast<uint32_t>(dims.size())};
  value.dims = dims;
  if (!dims.empty() && scope.array_tables != nullptr)
    value.outermost = UnpackedDimKind(dims.front(), *scope.array_tables);
  return value;
}

// §7.4.5: an element of an unpacked array is of the array's dimensions after
// the first, the outermost of which makes the kind of array it is in turn.
void DropOutermostDim(DeclaredValue& value, const ExprTypeScope& scope) {
  --value.unpacked_dims;
  if (value.dims.empty()) return;
  value.dims.erase(value.dims.begin());
  if (value.dims.empty() || scope.array_tables == nullptr) return;
  value.outermost = UnpackedDimKind(value.dims.front(), *scope.array_tables);
  value.index_type = IndexDimType(value.dims.front());
}

// §7.4.2 with §11.5.1: a select of the value `select` writes its base. An
// unpacked array's element is the array's type with one dimension fewer; a
// slice of one is an unpacked array still, of bounds §6.22.1(f) would match
// it by that no clause states.
std::optional<DeclaredValue> SelectedValue(const Expr* select,
                                           const ExprTypeScope& scope) {
  if (select->base == nullptr) return std::nullopt;
  std::optional<DeclaredValue> base = ValueOf(select->base, scope);
  // §6.23: an element of a dynamic object is no operand of a type reference.
  if (!base || base->outermost != UnpackedKind::kFixed) return std::nullopt;
  if (base->unpacked_dims == 0)
    return AsValue(PackedSelectType(base->type, select, scope));
  if (select->index_end != nullptr) return std::nullopt;
  DropOutermostDim(*base, scope);
  return base;
}

// §8.5 and §8.6: the member `name` of the class a handle of `handle` refers
// to, a property or a function's result.
std::optional<DeclaredValue> ClassMemberValue(const DataType& handle,
                                              std::string_view name,
                                              const ExprTypeScope& scope) {
  if (!scope.class_member) return std::nullopt;
  std::optional<UnpackedArrayType> member = scope.class_member(handle, name);
  if (!member) return std::nullopt;
  return UnderDims(std::move(member->element), member->dims, scope);
}

// §7.2 and §8.5: the member a member select names, of the type it is
// declared with and the unpacked dimensions it writes, a structure's or
// union's or a class's through a handle. Nothing for a package's or class's
// scope resolution, and for a base that is none of those.
std::optional<DeclaredValue> MemberValue(const Expr* access,
                                         const ExprTypeScope& scope) {
  if (access->is_scope_resolution || access->rhs == nullptr) {
    return std::nullopt;
  }
  std::optional<DeclaredValue> base = ValueOf(access->lhs, scope);
  if (!base || base->unpacked_dims != 0) return std::nullopt;
  const DataType* aggregate = ResolvedAggregateType(
      base->type, scope.typedefs, scope.constants, scope.arena);
  if (aggregate == nullptr)
    return ClassMemberValue(base->type, access->rhs->text, scope);
  auto member = std::ranges::find(aggregate->struct_members, access->rhs->text,
                                  &StructMember::name);
  if (member == aggregate->struct_members.end()) return std::nullopt;
  return UnderDims(MemberWrittenType(*member), member->unpacked_dims, scope);
}

// §6.16.1 to §6.16.10: the type each string method that gives a value gives,
// by the name of the type.
using TypeNameByMethod = std::pair<std::string_view, std::string_view>;
constexpr std::array<TypeNameByMethod, 12> kStringMethodTypes = {
    {{"len", "int"},
     {"getc", "byte"},
     {"toupper", "string"},
     {"tolower", "string"},
     {"compare", "int"},
     {"icompare", "int"},
     {"substr", "string"},
     {"atoi", "integer"},
     {"atohex", "integer"},
     {"atooct", "integer"},
     {"atobin", "integer"},
     {"atoreal", "real"}}};

// §6.19.5.1 to §6.19.5.4: the methods that give a value of the enumeration.
constexpr std::array<std::string_view, 4> kEnumerationSteps = {"first", "last",
                                                               "next", "prev"};

// §7.9.1 to §7.9.7: the methods of an associative array that give an int.
constexpr std::array<std::string_view, 7> kAssociativeIntMethods = {
    "num", "size", "exists", "first", "last", "next", "prev"};

// §7.12.1: the array locator methods that give a queue of the array's
// elements, and those that give a queue of their indexes.
constexpr std::array<std::string_view, 6> kElementLocators = {
    "find", "find_first", "find_last", "min", "max", "unique"};
constexpr std::array<std::string_view, 4> kIndexLocators = {
    "find_index", "find_first_index", "find_last_index", "unique_index"};

// §7.12.3: the array reduction methods.
constexpr std::array<std::string_view, 5> kReductionMethods = {
    "sum", "product", "and", "or", "xor"};

std::optional<DataType> StringMethodType(std::string_view method) {
  auto it =
      std::ranges::find(kStringMethodTypes, method, &TypeNameByMethod::first);
  if (it == kStringMethodTypes.end()) return std::nullopt;
  return TypeNameToDataType(it->second);
}

std::optional<DataType> EnumerationMethodType(const DataType& enumeration,
                                              std::string_view method) {
  if (std::ranges::find(kEnumerationSteps, method) != kEnumerationSteps.end())
    return enumeration;
  if (method == "num") return TypeNameToDataType("int");
  if (method == "name") return TypeNameToDataType("string");
  return std::nullopt;
}

// §7.5.2, §7.10.2.1 and §7.9.1 to §7.9.7: whether `method` of an array whose
// outermost dimension makes an array of kind `kind` gives an int.
bool GivesAnInt(UnpackedKind kind, std::string_view method) {
  if (kind == UnpackedKind::kAssociative) {
    return std::ranges::find(kAssociativeIntMethods, method) !=
           kAssociativeIntMethods.end();
  }
  return kind != UnpackedKind::kFixed && method == "size";
}

// §7.12: the iterator a with clause reads, named by the method's argument, or
// item where the method is written with none.
std::string_view IteratorName(const Expr* host) {
  if (host->kind == ExprKind::kCall && !host->args.empty() &&
      host->args.front() != nullptr &&
      host->args.front()->kind == ExprKind::kIdentifier) {
    return host->args.front()->text;
  }
  return "item";
}

// §7.12.3: the type of the with clause of `host`, a reduction of `array`, in
// which the iterator stands for an element of the array, and its index method
// gives an int, or an associative array's index type (§7.12.4).
std::optional<DataType> WithClauseType(const Expr* host,
                                       const DeclaredValue& array,
                                       const ExprTypeScope& scope) {
  const std::string_view kIterator = IteratorName(host);
  const DeclaredValue kElement{array.type, array.unpacked_dims - 1};
  ExprTypeScope within = scope;
  within.value_named =
      [&](std::string_view name) -> std::optional<DeclaredValue> {
    if (name == kIterator) return kElement;
    return scope.value_named(name);
  };
  within.iterator = kIterator;
  within.iterator_index = array.outermost == UnpackedKind::kAssociative
                              ? array.index_type
                              : TypeNameToDataType("int");
  return ExprSelfType(host->with_expr, within);
}

// §7.12.3: a reduction gives the array's element type, or the type of its with
// clause's expression where one is written.
std::optional<DataType> ReductionType(const Expr* host,
                                      const DeclaredValue& array,
                                      const ExprTypeScope& scope) {
  if (host->with_expr != nullptr) return WithClauseType(host, array, scope);
  if (array.unpacked_dims != 1) return std::nullopt;
  return array.type;
}

std::optional<DataType> ArrayMethodType(const Expr* host,
                                        std::string_view method,
                                        const DeclaredValue& array,
                                        const ExprTypeScope& scope) {
  if (std::ranges::find(kReductionMethods, method) != kReductionMethods.end())
    return ReductionType(host, array, scope);
  if (GivesAnInt(array.outermost, method)) return TypeNameToDataType("int");
  // §7.10.2.4 and §7.10.2.5: a queue's pop_front and pop_back give an
  // element of the queue.
  bool pops = method == "pop_front" || method == "pop_back";
  if (!pops || array.outermost != UnpackedKind::kQueue ||
      array.unpacked_dims != 1) {
    return std::nullopt;
  }
  return array.type;
}

// Whether `receiver` names the iterator of the with clause `scope` reads.
bool IsIterator(const Expr* receiver, const ExprTypeScope& scope) {
  return !scope.iterator.empty() && receiver != nullptr &&
         receiver->kind == ExprKind::kIdentifier &&
         receiver->text == scope.iterator;
}

// The type a call of a built-in method gives, `host` being the call, or the
// member access naming the method where the call leaves out its parentheses
// (§5.13): by the method's name and the value it is called on, a string, an
// enumeration or an array. Nothing for a method that gives no value, and for
// a value it is no method of.
std::optional<DataType> BuiltinMethodType(const Expr* host,
                                          const ExprTypeScope& scope) {
  const Expr* member = BuiltinMethodMember(host);
  if (member == nullptr) return std::nullopt;
  const std::string_view kMethod = member->rhs->text;
  if (kMethod == "index" && IsIterator(member->lhs, scope))
    return scope.iterator_index;
  std::optional<DeclaredValue> receiver = ValueOf(member->lhs, scope);
  if (!receiver) return std::nullopt;
  if (receiver->unpacked_dims != 0)
    return ArrayMethodType(host, kMethod, *receiver, scope);
  DataTypeKind kind = ResolvedTypeKind(receiver->type, scope.typedefs);
  if (kind == DataTypeKind::kString) return StringMethodType(kMethod);
  if (kind == DataTypeKind::kEnum)
    return EnumerationMethodType(receiver->type, kMethod);
  return std::nullopt;
}

// §7.10: a queue, `[$]` its own dimension, outermost, of elements of
// `element` under the dimensions `inner`, the `$` made in `arena`.
UnpackedArrayType QueueOf(DataType element, std::span<Expr* const> inner,
                          Arena& arena) {
  auto* queue = arena.Create<Expr>();
  queue->kind = ExprKind::kIdentifier;
  queue->text = "$";
  std::vector<Expr*> dims{queue};
  dims.insert(dims.end(), inner.begin(), inner.end());
  return UnpackedArrayType{std::move(element), std::move(dims)};
}

// §7.12.1: the queue an array locator method's call `host` gives, of the
// array's elements or of an index of one: an int, or an associative array's
// index type. Nothing where `host` calls no locator method, and for an array
// whose dimensions, or whose index type, are not recorded.
std::optional<UnpackedArrayType> LocatorType(const Expr* host,
                                             const ExprTypeScope& scope) {
  const Expr* member = BuiltinMethodMember(host);
  if (member == nullptr) return std::nullopt;
  const std::string_view kMethod = member->rhs->text;
  const bool kElements =
      std::ranges::find(kElementLocators, kMethod) != kElementLocators.end();
  if (!kElements &&
      std::ranges::find(kIndexLocators, kMethod) == kIndexLocators.end()) {
    return std::nullopt;
  }
  std::optional<DeclaredValue> array = ValueOf(member->lhs, scope);
  if (!array || array->unpacked_dims == 0 ||
      array->dims.size() != array->unpacked_dims) {
    return std::nullopt;
  }
  if (kElements) {
    return QueueOf(array->type, std::span(array->dims).subspan(1), scope.arena);
  }
  if (array->outermost != UnpackedKind::kAssociative)
    return QueueOf(TypeNameToDataType("int"), {}, scope.arena);
  if (!array->index_type) return std::nullopt;
  return QueueOf(*array->index_type, {}, scope.arena);
}

// A `.` selects a member of a structure or union, or else, without
// parentheses, calls a built-in method.
std::optional<DeclaredValue> MemberOrMethodValue(const Expr* access,
                                                 const ExprTypeScope& scope) {
  if (std::optional<DeclaredValue> member = MemberValue(access, scope))
    return member;
  return AsValue(BuiltinMethodType(access, scope));
}

std::optional<DeclaredValue> ValueOf(const Expr* expr,
                                     const ExprTypeScope& scope) {
  if (expr == nullptr) return std::nullopt;
  switch (expr->kind) {
    case ExprKind::kIdentifier:
      if (!expr->scope_prefix.empty()) return std::nullopt;
      return scope.value_named(expr->text);
    case ExprKind::kSelect:
      return SelectedValue(expr, scope);
    case ExprKind::kMemberAccess:
      return MemberOrMethodValue(expr, scope);
    default:
      return AsValue(ExprSelfType(expr, scope));
  }
}

// A call of a built-in method, of a class's method through a handle (§8.6),
// or of a function the scope declares.
std::optional<DataType> CallType(const Expr* call, const ExprTypeScope& scope) {
  if (std::optional<DataType> builtin = BuiltinMethodType(call, scope))
    return builtin;
  const Expr* method = call->lhs;
  if (method != nullptr && method->kind == ExprKind::kMemberAccess &&
      !method->is_scope_resolution) {
    std::optional<DeclaredValue> result = MemberValue(method, scope);
    if (!result || result->unpacked_dims != 0) return std::nullopt;
    return std::move(result->type);
  }
  return scope.call_returns(call);
}

// A name, a select or a member: the value's type, nothing for an unpacked
// array.
std::optional<DataType> WholeValueType(const Expr* expr,
                                       const ExprTypeScope& scope) {
  std::optional<DeclaredValue> value = ValueOf(expr, scope);
  if (!value || value->unpacked_dims != 0) return std::nullopt;
  return std::move(value->type);
}

// §6.24.1 and §11.7: the operand `operand` with the signing a signing cast,
// $signed or $unsigned names.
std::optional<DataType> Resigned(const Expr* operand, bool is_signed,
                                 const ExprTypeScope& scope) {
  std::optional<Shape> shape = OperandShape(operand, scope);
  if (!shape || IsReal(*shape)) return std::nullopt;
  shape->is_signed = is_signed;
  return TypeOfShape(*shape, scope.arena);
}

// §6.24.1: a size cast, its operand's signing and state at the size it names.
std::optional<DataType> SizeCastType(const Expr* cast,
                                     const ExprTypeScope& scope) {
  std::optional<int64_t> size = ConstEvalInt(cast->rhs, scope.constants);
  std::optional<Shape> operand = OperandShape(cast->lhs, scope);
  if (!size || *size <= 0 || !operand || IsReal(*operand)) return std::nullopt;
  return TypeOfShape(
      {static_cast<uint32_t>(*size), operand->is_signed, operand->four_state},
      scope.arena);
}

// Whether `name` is a type: a built-in keyword or a typedef of the scope.
bool IsTypeName(std::string_view name, const TypedefMap& typedefs) {
  return TypeNameToDataType(name).kind != DataTypeKind::kNamed ||
         typedefs.contains(name);
}

// §6.24.1: a cast whose casting type the parser kept as an expression: a type
// reference, a name, a package's or class's typedef behind its scope, or a
// size.
std::optional<DataType> CastToWrittenType(const Expr* cast,
                                          const ExprTypeScope& scope) {
  const Expr* target = cast->rhs;
  if (target->kind == ExprKind::kTypeRef) return scope.type_ref(target);
  if (target->kind == ExprKind::kIdentifier &&
      IsTypeName(target->text, scope.typedefs)) {
    return TypeNameToDataType(target->text);
  }
  if (target->kind == ExprKind::kMemberAccess && target->is_scope_resolution &&
      target->lhs != nullptr && target->rhs != nullptr) {
    DataType named;
    named.kind = DataTypeKind::kNamed;
    named.scope_name = target->lhs->text;
    named.type_name = target->rhs->text;
    return named;
  }
  return SizeCastType(cast, scope);
}

// §6.24.1: the type a cast converts its operand to.
std::optional<DataType> CastType(const Expr* cast, const ExprTypeScope& scope) {
  if (cast->text == "signed" || cast->text == "unsigned")
    return Resigned(cast->lhs, cast->text == "signed", scope);
  if (cast->text == "const") return ExprSelfType(cast->lhs, scope);
  if (!cast->text.empty()) return TypeNameToDataType(cast->text);
  if (cast->rhs == nullptr) return std::nullopt;
  return CastToWrittenType(cast, scope);
}

std::optional<DataType> FirstArgumentType(const Expr* call,
                                          const ExprTypeScope& scope) {
  if (call->args.empty()) return std::nullopt;
  return ExprSelfType(call->args.front(), scope);
}

std::optional<DataType> SystemCallType(const Expr* call,
                                       const ExprTypeScope& scope) {
  if (call->callee == "$signed" || call->callee == "$unsigned") {
    if (call->args.empty()) return std::nullopt;
    return Resigned(call->args.front(), call->callee == "$signed", scope);
  }
  auto listed = std::ranges::find(kSystemFunctionTypes, call->callee,
                                  &SystemFunctionType::name);
  if (listed != kSystemFunctionTypes.end()) {
    const SelfType& result = listed->type;
    return TypeOfShape({result.width, result.is_signed, result.four_state},
                       scope.arena);
  }
  if (std::ranges::find(kArgumentTypedFunctions, call->callee) !=
      kArgumentTypedFunctions.end()) {
    return FirstArgumentType(call, scope);
  }
  if (std::ranges::find(kRealSystemFunctions, call->callee) !=
      kRealSystemFunctions.end()) {
    return TypeNameToDataType("real");
  }
  return std::nullopt;
}

// §5.9: eight bits a character, an empty string being one character wide.
DataType StringLiteralType(const Expr* literal, Arena& arena) {
  std::optional<std::string> characters = ConstEvalString(literal);
  size_t count = characters ? std::max<size_t>(characters->size(), 1) : 1;
  return TypeOfShape({static_cast<uint32_t>(8 * count), false, true}, arena);
}

std::optional<DataType> UnaryType(const Expr* unary,
                                  const ExprTypeScope& scope) {
  if (unary->op == TokenKind::kPlusPlus || unary->op == TokenKind::kMinusMinus)
    return ExprSelfType(unary->lhs, scope);
  std::optional<Shape> operand = OperandShape(unary->lhs, scope);
  if (!operand) return std::nullopt;
  if (IsUnaryReductionOp(unary->op) || unary->op == TokenKind::kBang)
    return TypeOfShape(OneBit(operand->four_state), scope.arena);
  return TypeOfShape(*operand, scope.arena);
}

std::optional<DataType> BinaryType(const Expr* binary,
                                   const ExprTypeScope& scope) {
  if (binary->op == TokenKind::kEq || IsCompoundAssignOp(binary->op))
    return ExprSelfType(binary->lhs, scope);
  std::optional<Shape> left = OperandShape(binary->lhs, scope);
  std::optional<Shape> right = OperandShape(binary->rhs, scope);
  if (!left || !right) return std::nullopt;
  if (IsMaxWidthBinaryOp(binary->op))
    return TypeOfShape(Widest(*left, *right), scope.arena);
  if (IsLeftWidthBinaryOp(binary->op))
    return TypeOfShape(LeftSized(*left, *right), scope.arena);
  return TypeOfShape(OneBit(left->four_state || right->four_state),
                     scope.arena);
}

// §11.4.11: as wide as the wider result, signed where both are, 4-state where
// the condition or a result is.
std::optional<DataType> ConditionalType(const Expr* conditional,
                                        const ExprTypeScope& scope) {
  std::optional<Shape> condition = OperandShape(conditional->condition, scope);
  std::optional<Shape> chosen = OperandShape(conditional->true_expr, scope);
  std::optional<Shape> other = OperandShape(conditional->false_expr, scope);
  if (!condition || !chosen || !other) return std::nullopt;
  Shape result = Widest(*chosen, *other);
  result.four_state = result.four_state || condition->four_state;
  return TypeOfShape(result, scope.arena);
}

// §11.4.12: the operands of a concatenation side by side, unsigned.
std::optional<Shape> JoinedShape(const std::vector<Expr*>& operands,
                                 const ExprTypeScope& scope) {
  Shape joined;
  for (const Expr* operand : operands) {
    std::optional<Shape> part = OperandShape(operand, scope);
    if (!part || IsReal(*part)) return std::nullopt;
    joined.width += part->width;
    joined.four_state = joined.four_state || part->four_state;
  }
  if (joined.width == 0) return std::nullopt;
  return joined;
}

std::optional<DataType> ConcatenationType(const Expr* concatenation,
                                          const ExprTypeScope& scope) {
  std::optional<Shape> joined = JoinedShape(concatenation->elements, scope);
  if (!joined) return std::nullopt;
  return TypeOfShape(*joined, scope.arena);
}

// §11.4.12.1: the count of copies of the operands' concatenation.
std::optional<DataType> ReplicationType(const Expr* replication,
                                        const ExprTypeScope& scope) {
  std::optional<int64_t> count =
      ConstEvalInt(replication->repeat_count, scope.constants);
  std::optional<Shape> joined = JoinedShape(replication->elements, scope);
  if (!count || *count <= 0 || !joined) return std::nullopt;
  joined->width *= static_cast<uint32_t>(*count);
  return TypeOfShape(*joined, scope.arena);
}

// Whether an item of a set membership's range list is 4-state, a range
// `[low:high]` being so where either bound is; nothing for an item the scope
// does not type.
std::optional<bool> RangeItemFourState(const Expr* item,
                                       const ExprTypeScope& scope) {
  if (item->kind == ExprKind::kSelect && item->base == nullptr) {
    std::optional<Shape> low = OperandShape(item->index, scope);
    std::optional<Shape> high = OperandShape(item->index_end, scope);
    if (!low || !high) return std::nullopt;
    return low->four_state || high->four_state;
  }
  std::optional<Shape> shape = OperandShape(item, scope);
  if (!shape) return std::nullopt;
  return shape->four_state;
}

// §11.4.13: one unsigned bit, 4-state where an operand is.
std::optional<DataType> InsideType(const Expr* inside,
                                   const ExprTypeScope& scope) {
  std::optional<Shape> tested = OperandShape(inside->lhs, scope);
  if (!tested) return std::nullopt;
  bool four_state = tested->four_state;
  for (const Expr* item : inside->elements) {
    std::optional<bool> item_four_state = RangeItemFourState(item, scope);
    if (!item_four_state) return std::nullopt;
    four_state = four_state || *item_four_state;
  }
  return TypeOfShape(OneBit(four_state), scope.arena);
}

// §5.7.1: as wide as its size, signed where decimal or written with the s
// designator, 4-state.
DataType IntegerLiteralType(const Expr* literal, Arena& arena) {
  return TypeOfShape(
      {ConstLiteralWidth(literal), IsSignedLiteral(literal->text), true},
      arena);
}

}  // namespace

DataType VectorType(uint32_t width, bool is_signed, bool four_state,
                    Arena& arena) {
  DataType type;
  type.kind = four_state ? DataTypeKind::kLogic : DataTypeKind::kBit;
  type.is_signed = is_signed;
  if (width > 1) {
    type.packed_dim_left = IntLiteral(arena, width - 1);
    type.packed_dim_right = IntLiteral(arena, 0);
  }
  return type;
}

std::optional<UnpackedArrayType> ValueArrayType(const DeclaredValue& value) {
  if (value.dims.size() != value.unpacked_dims) return std::nullopt;
  return UnpackedArrayType{value.type, value.dims};
}

std::optional<UnpackedArrayType> ExprSelfArrayType(const Expr* expr,
                                                   const ExprTypeScope& scope) {
  if (std::optional<UnpackedArrayType> located = LocatorType(expr, scope))
    return located;
  std::optional<DeclaredValue> value = ValueOf(expr, scope);
  if (!value) return std::nullopt;
  return ValueArrayType(*value);
}

std::optional<DataType> ExprSelfType(const Expr* expr,
                                     const ExprTypeScope& scope) {
  if (expr == nullptr) return std::nullopt;
  switch (expr->kind) {
    case ExprKind::kIdentifier:
    case ExprKind::kSelect:
    case ExprKind::kMemberAccess:
      return WholeValueType(expr, scope);
    case ExprKind::kCall:
      return CallType(expr, scope);
    case ExprKind::kCast:
      return CastType(expr, scope);
    case ExprKind::kSystemCall:
      return SystemCallType(expr, scope);
    case ExprKind::kIntegerLiteral:
      return IntegerLiteralType(expr, scope.arena);
    case ExprKind::kUnbasedUnsizedLiteral:
      return TypeOfShape(OneBit(true), scope.arena);
    case ExprKind::kRealLiteral:
    case ExprKind::kTimeLiteral:
      return TypeNameToDataType("real");
    case ExprKind::kStringLiteral:
      return StringLiteralType(expr, scope.arena);
    case ExprKind::kPostfixUnary:
      return ExprSelfType(expr->lhs, scope);
    case ExprKind::kUnary:
      return UnaryType(expr, scope);
    case ExprKind::kBinary:
      return BinaryType(expr, scope);
    case ExprKind::kTernary:
      return ConditionalType(expr, scope);
    case ExprKind::kConcatenation:
      return ConcatenationType(expr, scope);
    case ExprKind::kReplicate:
      return ReplicationType(expr, scope);
    case ExprKind::kInside:
      return InsideType(expr, scope);
    case ExprKind::kMinTypMax:
      return ExprSelfType(SelectMinTypMaxMember(expr), scope);
    default:
      return std::nullopt;
  }
}

}  // namespace delta
