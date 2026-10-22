#pragma once

#include <cstdint>
#include <string_view>
#include <unordered_map>
#include <unordered_set>

#include "elaborator/const_eval.h"

namespace delta {

struct DataType;
enum class DataTypeKind : uint8_t;
class Arena;
struct PackageDecl;
struct ClassDecl;
struct ModuleItem;

using TypedefMap = std::unordered_map<std::string_view, DataType>;

// §7.2.1 / §23.6: fill in `nested_type` for every struct/union member of `dt`
// whose declared type is a named typedef resolving to a struct or union, so the
// aggregate's layout is fully self-describing (the simulator can size and reach
// a nested member by its dotted path without a typedef table). Recurses into
// the resolved members; arena-copies each resolved type so `dt` owns it.
void ResolveNestedAggregateTypes(DataType& dt, const TypedefMap& typedefs,
                                 Arena& arena);

// §7.2 with §8.4: give every member of `dt` whose type names a class in
// `class_names`, by its own name or through a chain of typedefs ending at it
// (§6.18), the width of the handle it holds, kClassMemberHandleWidth, and
// record the class's name as its type. A class's name is no typedef's, so the
// member otherwise stays unresolved and is sized as a one-bit vector, or, held
// under a typedef of the class, as no bits at all.
void SizeClassHandleMembers(
    DataType& dt, const TypedefMap& typedefs,
    const std::unordered_set<std::string_view>& class_names);

// §7.2.1 with §6.18: the packed structure or union a declared type stands for,
// laid out for a member select -- an arena copy of the type itself when the
// declaration wrote one, or of the one a typedef name resolves to through the
// typedef table, followed through a name standing for another name, with its
// nested member types resolved as ResolveNestedAggregateTypes leaves them. Null
// for a type of any other kind, for a name the table does not hold and for an
// aggregate with no members. A variable, a port and a net of an aggregate type
// each carry the same layout, so all three resolve it here. §6.20: the copy's
// members have their dimensions folded against `scope`, the parameters of the
// instance declaring it, as a typedef's were where it was recorded. Defined in
// src/elaborator/type_eval_aggregate.cpp.
const DataType* ResolvedAggregateType(const DataType& dtype,
                                      const TypedefMap& typedefs,
                                      const ScopeMap& scope, Arena& arena);

// §6.18 and §6.6.7: the packed vector type `dtype`, a typedef or nettype name,
// stands for through a chain of names, as an arena copy; null where the name
// stands for an enumeration, a type with no packed dimension, or nothing the
// table holds. An enumeration's range is its base type's, not its own. A
// net of such a name takes the range the type declares, as a variable does
// (§37.16 detail 3). Defined in src/elaborator/type_eval_aggregate.cpp.
const DataType* NamedPackedVectorType(const DataType& dtype,
                                      const TypedefMap& typedefs, Arena& arena);

// §7.2 with §6.20 and §11.2.1: `type`'s members with every dimension folded
// against `scope` -- each packed bound, each unpacked `[size]` or
// `[left:right]`, a queue's `[$:bound]` bound, and those of a nested
// aggregate's or enumeration's type -- as an arena literal, a dimension that
// does not fold, an associative one's type among them, kept as written. The
// readers of a member's dimensions fold them with no scope, so a member sized
// by a parameter reaches them sized only once this has run. New expressions
// and a new nested type are made rather than the old changed, so a type copied
// from a source tree several instances share leaves that tree as it was.
// Defined in src/elaborator/type_eval_aggregate.cpp.
void FoldMemberDims(DataType& type, const ScopeMap& scope, Arena& arena);

// §7.4.4: the element count of the packed dimensions a declaration writes --
// the leading range times each further one -- which is what a use-site
// dimension multiplies the width of the type it is written on by. Zero where
// the declaration carries no packed dimension or a bound does not fold.
uint32_t PackedDimProduct(const DataType& dtype);

// The same product with each bound folded against `scope`, so a bound naming
// a parameter resolves; zero where a bound does not fold.
uint32_t PackedDimProduct(const DataType& dtype, const ScopeMap& scope);

uint32_t EvalTypeWidth(const DataType& dtype);

// §7.4.1: the enumeration `dtype` writes, without the packed dimensions after
// its body that make a packed array of it; `dtype` itself where it has none.
DataType EnumArrayElement(const DataType& dtype);

// §10.9.1's `type:value` key. IsTypeKeyword answers whether a key names a type
// at all -- the alternative being an index key -- and TypeKeyMatchesKind
// whether that type is the one an element is declared with, which is what
// decides whether the key covers the element: a type:value gives an explicit
// value to each structure field whose type matches, and §10.9.1 applies the
// same rule to an array's elements. They live here rather than beside either
// user because both the elaborator, which reports a pattern that covers no
// element, and the simulator, which fills the ones a key does cover, have to
// answer the same question the same way; two copies of the keyword list had
// already drifted apart on the second predicate, the elaborator's copy having
// only the first.
// §6.16/§6.18: whether the declared type is a string, whether written as the
// keyword or reached through a typedef name. Is4stateType beside it resolves a
// name the same way and for the same reason.
bool IsStringType(const DataType& type, const TypedefMap& typedefs);

bool IsTypeKeyword(std::string_view key);
bool TypeKeyMatchesKind(std::string_view key, DataTypeKind kind);

// §7.2 with §6.16: the width a string member of an unpacked structure takes
// in the structure's packed value, which holds a handle to the member's text
// rather than the text itself, a string being of any length.
inline constexpr uint32_t kStringMemberHandleWidth = 64;

// §7.2 with §7.5: the width a member of an unpacked structure declared as a
// dynamic array takes in the structure's packed value, which holds a handle
// to the member's elements (DynMemberQueue in
// src/simulator/dyn_struct_member.h), their count being of no fixed size.
inline constexpr uint32_t kDynamicMemberHandleWidth = 64;

// §7.2 with §8.4: the width a member of an unpacked structure declared with a
// class type takes in the structure's packed value, the handle of the object
// it refers to, as wide as a variable of the class holds.
inline constexpr uint32_t kClassMemberHandleWidth = 64;

struct StructMember;
uint32_t EvalStructMemberWidth(const StructMember& m);
// §7.2 with §7.4.2: the number of elements an unpacked array member of a
// structure or union holds, the product of its unpacked dimensions; 1 for a
// member that is no array, or whose dimensions do not fold. A member takes
// EvalStructMemberWidth bits per element.
uint32_t UnpackedMemberCount(const StructMember& m);
// §7.2 with §7.5 and §7.10: whether the member is declared as a dynamically
// sized array, its one unpacked dimension a dynamic array's `[]` or a queue's
// `[$]` or `[$:N]`.
bool IsDynamicArrayMember(const StructMember& m);
// The bits a member takes in its structure's packed value: a dynamic array
// member's handle, else EvalStructMemberWidth bits per element of it.
uint32_t StructMemberStorageWidth(const StructMember& m);
// The bounds of a one-dimensional unpacked array member, left first, the size
// form `[n]` as [0:n-1]. False for a member of none or of several dimensions,
// or one whose bounds do not fold.
bool UnpackedMemberBounds(const StructMember& m, int64_t* left, int64_t* right);
uint32_t EvalStructMemberWidth(const StructMember& m,
                               const TypedefMap& typedefs);
uint32_t StructMemberStorageWidth(const StructMember& m,
                                  const TypedefMap& typedefs);
// §7.2.1 and §7.3.1: the bits a structure's or union's members take together,
// a structure's summed and a union's the widest, with a packed tagged union's
// tag; each member's dimensions folded with no scope. Its own packed
// dimensions, which make an array of it, are the caller's.
uint32_t EvalStructOrUnionWidth(const DataType& dtype,
                                const TypedefMap& typedefs);
// The same with the members' dimensions folded against `scope` first
// (FoldMemberDims), in a scratch arena the call releases. Defined in
// src/elaborator/type_eval_aggregate.cpp.
uint32_t FoldedMembersWidth(const DataType& dtype, const TypedefMap& typedefs,
                            const ScopeMap& scope);

uint32_t TaggedUnionTagWidth(const DataType& dtype);
uint32_t TaggedUnionTagBitOffset(const DataType& dtype);

// The typedef a named type denotes, looked up under its "Scope::name" key
// where the name was written with a class or package prefix (§8.23, §26.3)
// and under the bare name otherwise; null for an unnamed type or a name the
// table does not hold. A prefixed name never falls back to the bare one:
// that would take the layout from a different type.
const DataType* FindNamedType(const DataType& dtype,
                              const TypedefMap& typedefs);

// §6.18 with §23.9: enters the typedef `name`, declared with `type`, into
// `typedefs`. A typedef writing its own bare name as its type names the type
// the name stood for before it, so the table keeps that entry, with any packed
// dimensions the typedef writes added outside its own, or keeps none where the
// name stands for a class.
void RecordTypedef(TypedefMap& typedefs, std::string_view name,
                   const DataType& type);

// §26.2 with §6.18: `type`, the type a typedef of the package `package` was
// declared with, its name written behind the package's scope where it names a
// typedef the package declares, so it is looked up under the package's
// "package::name" key and never among the names of a scope importing the
// package, which may declare one of its own under that name.
DataType InPackageScope(const DataType& type, const PackageDecl& package);

// §8.23 with §6.18: `type`, as a member of the class `cls` is declared with
// it, its name written behind the class's scope where it names a typedef the
// class declares, so it is looked up under the "Class::name" key
// RegisterClassTypedefs records and never as a typedef of the scope around
// the class, which may declare one of its own under that name.
DataType InClassScope(const DataType& type, const ClassDecl& cls);

// The same, `scope` being the path the class's typedefs are keyed under, as
// RegisterClassTypedefKeys builds it: "Outer::Inner" for a class nested in
// another (§8.23), whose typedefs stand under "Outer::Inner::name".
DataType InClassScope(const DataType& type, const ClassDecl& cls,
                      std::string_view scope);

// The typedef names in scope at a point of a class or a package, each with the
// key of the class or package declaring it: the scope's own typedefs declared
// so far, and for a class those its base classes declare (§8.13), a nearer
// class's hiding a farther one's.
using TypedefScopes = std::unordered_map<std::string_view, std::string_view>;

// §23.9 with §6.18: a typedef's type as the class or package declaring it
// records it, written as the bare name of a typedef in `scopes` put behind the
// key of the scope declaring that typedef, and so each member of a structure
// or union, in an aggregate written inline within a member as well. A class
// or a package opens a scope, and a name inside it finds the scope's own
// typedef, or one a class inherits, before one around the scope. The scope's
// own typedefs enter `scopes` as they are declared, since a typedef is in
// scope only from its declaration on, which also keeps a typedef from naming
// itself. Each inline aggregate is copied into `arena` before it is scoped,
// so the type as written is left alone.
DataType InTypedefScopes(const DataType& type, const TypedefScopes& scopes,
                         Arena& arena);

// §6.18: enters `td`, a typedef the class or package keyed `scope` declares,
// into `scopes` under its name, unless it is a forward typedef, which names a
// type defined elsewhere rather than defining one under the scope's key.
void EnterTypedefScope(TypedefScopes& scopes, const ModuleItem& td,
                       std::string_view scope);

// §23.9 with §26.3: the type of `item`, a typedef `pkg` declares, as the
// package records it under its "package::name" key and an import of it enters
// it under its bare name: its own name written through the package where the
// package declares a typedef of it (InPackageScope), and each member of a
// structure or union written as the name of a typedef the package declares
// ahead of `item` put behind the package's name (InTypedefScopes).
DataType PackageTypedefType(const ModuleItem& item, const PackageDecl& pkg,
                            Arena& arena);

// The type `dtype` stands for, following each typedef or user-defined nettype
// name (§6.18, §6.6.7) to the type it was declared with as far as the table
// holds one: a type, or the last name on the way the table holds nothing for,
// a class's among them.
const DataType& LastTypeInChain(const DataType& dtype,
                                const TypedefMap& typedefs);

// The kind of the type `dtype` stands for, following each typedef or
// user-defined nettype name (§6.18, §6.6.7) to the type it was declared with;
// the kind as written for a type no name stands for.
DataTypeKind ResolvedTypeKind(const DataType& dtype,
                              const TypedefMap& typedefs);

// The type `dtype` stands for at the end of its chain of typedef and nettype
// names, as ResolvedTypeKind follows it; null where a name on the way stands
// for nothing the table holds or the chain runs through one name twice.
const DataType* TypeAtChainEnd(const DataType& dtype,
                               const TypedefMap& typedefs);

// The same for a structure or union member's named type (§7.2.1): a member
// written behind a qualifier, `q::pair_t Add`, was looked up by `pair_t`
// alone, resolving to whatever a wildcard import made the bare name stand
// for, or to nothing. Defined with FindNamedType in
// src/elaborator/type_eval_named.cpp.
const DataType* MemberNamedType(const StructMember& m,
                                const TypedefMap& typedefs);

uint32_t EvalTypeWidth(const DataType& dtype, const TypedefMap& typedefs);

uint32_t EvalTypeWidth(const DataType& dtype, const TypedefMap& typedefs,
                       const ScopeMap& scope);

bool Is4stateType(DataTypeKind kind);

bool IsImplicitlySigned(DataTypeKind kind);

// §6.20.3/§6.23: map a type name (a built-in keyword like `int`/`shortint` or a
// user type/class name) to a DataType. Built-in scalar types map to their kind
// with the kind's implicit signedness; any other name becomes a kNamed type
// that resolves against the class/typedef tables later.
DataType TypeNameToDataType(std::string_view name);

bool Is4stateType(const DataType& dtype, const TypedefMap& typedefs);

bool IsSignedType(const DataType& dtype, const TypedefMap& typedefs);

struct Expr;

bool IsVector(const DataType& dtype);

bool IsVector(const DataType& dtype, const TypedefMap& typedefs);

bool IsSingularType(const DataType& dtype);

bool IsAggregateType(const DataType& dtype);

// §6.4: overloads that resolve a named type through the typedef table before
// classifying it, so an unpacked structure/union reached via a typedef name is
// still recognized as aggregate rather than mistaken for a singular named type.
bool IsSingularType(const DataType& dtype, const TypedefMap& typedefs);

bool IsAggregateType(const DataType& dtype, const TypedefMap& typedefs);

// §8.30.1: true when `tp` — a weak_reference#(T) type argument — denotes a
// class type. A bare class name matches directly; a typedef name is followed
// through the typedef table (up to a bounded depth) so an alias of a class is
// admitted just as the class name is. Built-in, non-class, or unresolved names
// yield false, which is the compiler-error path the rule requires.
bool WeakRefTypeParamNamesClass(
    const DataType& tp, const TypedefMap& typedefs,
    const std::unordered_set<std::string_view>& class_names);

bool IsIntegralType(DataTypeKind kind);

// §23.7 a) with §6.11 and §6.12: a kind of value with no members and no
// built-in methods -- an integral type that is no enumeration, or a real one.
bool IsMemberlessKind(DataTypeKind kind);

// §6.7.1: the net types, whose net declared with no data type takes the
// implicit logic type.
bool IsNetTypeKind(DataTypeKind kind);

bool IsSimpleBitVectorType(DataTypeKind kind);

bool IsSimpleBitVectorType(const DataType& dtype);

// §7.2 and §7.3: whether `type` is an unpacked structure or union, which is no
// integral value: neither declared packed nor a soft union (§7.3.1).
bool IsUnpackedAggregateType(const DataType& type);

bool TypesMatch(const DataType& a, const DataType& b);

bool TypesEquivalent(const DataType& a, const DataType& b);

// §6.22.2 — the element-type descriptor compared when deciding whether two
// array element types are equivalent: the kind, packed bit width, signedness,
// and whether the element is 4-state, and for an element type left as a name
// (an enumeration or a class) the name that identifies it.
struct ElementTypeInfo {
  DataTypeKind kind;
  uint32_t width;
  bool is_signed;
  bool is_4state;
  std::string_view type_name;
};

bool ElementTypesEquivalent(const ElementTypeInfo& a, const ElementTypeInfo& b);

bool IsAssignmentCompatible(const DataType& a, const DataType& b);

bool IsCastCompatible(const DataType& a, const DataType& b);

bool IsTypeIncompatible(const DataType& a, const DataType& b);

// Returns the bit width implied by a cast target type name (built-in keyword or
// a leading decimal width such as "12"); returns 0 for "string" and any name
// that has no fixed bit width. Defined once in type_eval.cpp.
uint32_t CastTargetWidth(std::string_view type_name);

uint32_t InferExprWidth(const Expr* expr, const TypedefMap& typedefs);

uint32_t ContextWidth(const Expr* expr, uint32_t ctx_width,
                      const TypedefMap& typedefs);

}  // namespace delta
