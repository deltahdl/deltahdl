#pragma once

#include <cstdint>
#include <functional>
#include <optional>
#include <string>
#include <string_view>

#include "elaborator/rtlir.h"
#include "parser/ast_type.h"

namespace delta {

struct Expr;

// §20.6.1 (printed pages 628-629 of IEEE 1800-2023): $typename returns the
// resolved type of its argument, a data type or an expression, as a string
// built by the clause's steps: a typedef resolved back to the type it names
// (a), the default signing removed (b), a system-generated name for an
// anonymous structure, union or enumeration (c), a "$" for the name of an
// unpacked array (d), each enumeration constant's value appended (e), a
// user-defined type name prefixed with its scope (f), ranges as unsized
// decimals (g), and white space reduced to a single space between identifiers
// and keywords (h). The run answers $typename from the running design, and the
// elaborator folds it in a constant expression from the declarations of the
// module being elaborated, so the steps ask what they need to know of the
// place a type is written in of a TypenameEnvironment each fills in its own
// way.

// §11.6.1 with §11.8.1: the self-determined type of an expression -- its
// width, its signedness and whether it is 4-state -- where its form gives one.
// `known` is false for a form that is not read.
struct SelfType {
  uint32_t width = 0;
  bool is_signed = false;
  bool four_state = false;
  bool known = false;
};

// What the steps ask of the place a type is written in.
struct TypenameEnvironment {
  // The value of a range's bound, a select's index or an enumeration
  // constant's initializer.
  std::function<int64_t(const Expr*)> value_of;
  // Step a: the type the typedef name written behind a scope (the first
  // argument, empty for none) stands for, null where no typedef declares it;
  // sets the third argument to the scope a package's typedef made visible by
  // an import is named behind (§26.3).
  std::function<const DataType*(std::string_view, std::string_view,
                                std::string&)>
      resolve_name;
  // Step f: the class a name no typedef resolves names, behind the package
  // declaring it; empty where it names no class a package declares.
  std::function<std::string(std::string_view, std::string_view)>
      qualified_class_name;
  // Step f: the name of the scope the type is written in, which the types it
  // declares are named behind.
  std::function<std::string_view()> scope_name;
  // Step e: the width of an enumeration's base type.
  std::function<uint32_t(const DataType&)> width_of;
  // The self-determined type of a variable named whole, unknown where it is
  // no variable of an integral type.
  std::function<SelfType(std::string_view)> name_self_type;
  // §11.4.11: whether an operand makes an expression real.
  std::function<bool(const Expr*)> is_real;
  // §7.4.1: the width of one element of the outermost packed dimension of the
  // variable named, which a select of it counts in; 1 for a vector of bits.
  std::function<uint32_t(std::string_view)> element_width;
};

struct TypenameParts;

// Writes a data type, or a structure's or union's member, as $typename does.
class TypenameWriter {
 public:
  explicit TypenameWriter(const TypenameEnvironment& env) : env_(env) {}

  // `scope` is the scope the declaration of the type was named behind, empty
  // where it is the one the type is written in, and `hint` names what declares
  // the type -- a variable, a member -- which is what an anonymous struct,
  // union or enum is named after (step c).
  std::string OfType(const DataType& type, std::string_view scope,
                     std::string_view hint);

  std::string OfMember(const StructMember& member, std::string_view scope);

 private:
  std::string PackedText(const TypenameParts& parts);
  std::string RangeText(const Expr* left, const Expr* right);
  std::string OfParts(const TypenameParts& parts, std::string_view scope,
                      std::string_view hint);
  std::string OfName(const TypenameParts& parts, std::string_view scope);
  std::string OfUnresolvedName(const TypenameParts& parts,
                               const std::string& prefix);
  std::string TypeOwnerPrefix(std::string_view prefix);
  std::string Anonymous(const DataType& type, std::string_view scope,
                        std::string_view hint);
  std::string OfStructUnionOrEnum(const DataType& type,
                                  const std::string& name);
  std::string OfEnum(const DataType& type);

  const TypenameEnvironment& env_;
};

// §20.6.1 Syntax 20-6's second form given a built-in type keyword, alone or
// with one packed range, `$typename(logic [7:0])`, which the parser reads as a
// name or as a range select over one: the type it names, signed as its keyword
// is by default; nothing for any other argument.
std::optional<DataType> KeywordTypeOf(const Expr* arg);

// Step d: a variable's unpacked dimensions as $typename writes them after the
// "$" standing for the array's name, "$[0:9]" for `AB_t AB[10]`; empty for a
// variable with none, or with one that did not fold to fixed bounds.
std::string UnpackedDimsText(const RtlirVariable& var);

// What UnpackedDimsText writes for one element of such an array: the
// dimensions after the first, behind the "$", or nothing where the first is
// the only one.
std::string ElementDimsText(std::string_view unpacked);

// §20.6.1 with §11.6.1 and §11.8.1: the self-determined type of an operator
// expression, a concatenation or a select, written as a vector of its width,
// `bit` where every operand is 2-state and `logic` where one is 4-state, and
// `real` where an operand makes it real (§11.4.11); empty where a part of it
// has a form that is not read.
std::string TypenameOfOperation(const Expr* arg,
                                const TypenameEnvironment& env);

}  // namespace delta
