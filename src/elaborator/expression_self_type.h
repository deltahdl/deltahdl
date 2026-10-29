#pragma once

#include <cstdint>
#include <functional>
#include <optional>
#include <string_view>
#include <vector>

#include "common/arena.h"
#include "elaborator/const_eval.h"
#include "elaborator/net_data_type.h"
#include "elaborator/type_eval.h"
#include "elaborator/unpacked_array_type.h"
#include "parser/ast_type.h"

namespace delta {

struct Expr;

// A value a name stands for: the data type its declaration writes, the
// number of unpacked dimensions the declaration writes after the name, which
// the data type does not carry, the kind of array the outermost of them
// makes, an associative array's index type (§7.8), and the unpacked
// dimensions themselves, outermost first, as the declaration writes them,
// empty where they are not recorded.
struct DeclaredValue {
  DataType type;
  uint32_t unpacked_dims = 0;
  UnpackedKind outermost = UnpackedKind::kFixed;
  std::optional<DataType> index_type = {};
  std::vector<Expr*> dims = {};
};

// What ExprSelfType reads the names an expression writes against.
struct ExprTypeScope {
  // The value a name written in the expression stands for -- a net, a
  // variable, a port, a parameter or an enumeration's named constant -- or
  // nothing.
  std::function<std::optional<DeclaredValue>(std::string_view)> value_named;
  // The type a call returns, or nothing where the call is of no function the
  // scope declares.
  std::function<std::optional<DataType>(const Expr*)> call_returns;
  // The type a type reference written in the expression stands for, as the
  // casting type of `type(x)'(y)`, or nothing.
  std::function<std::optional<DataType>(const Expr*)> type_ref;
  const TypedefMap& typedefs;
  // The constants a part-select's bounds, a replication's count and a size
  // cast's size fold against.
  const ScopeMap& constants;
  // Where the packed dimension of a type made for an operation is made.
  Arena& arena;
  // §7.12.4: within the with clause of an array manipulation method, the name
  // of its iterator, and the type the iterator's index method gives.
  std::string_view iterator = {};
  std::optional<DataType> iterator_index = {};
  // The typedefs' unpacked dimensions and the class names, which tell the
  // kind of array an unpacked dimension makes; null where no expression of an
  // unpacked array type is asked for.
  const TypeShapeTables* array_tables = nullptr;
  // §8.5 and §8.6: the type of the member a name selects of the class a
  // handle of the type given refers to: a property's type and unpacked
  // dimensions, or a function's return type; nothing where the type is no
  // class, or the class has no such member. Empty where no class is in reach.
  std::function<std::optional<UnpackedArrayType>(const DataType&,
                                                 std::string_view)>
      class_member = {};
};

// The bit or logic vector [width-1:0] of the signing given, a scalar where it
// is one bit wide, its bounds made in `arena`: the type ExprSelfType gives an
// operation, which §6.22.1 (b) matches against the built-in type of that
// width, signing and state.
DataType VectorType(uint32_t width, bool is_signed, bool four_state,
                    Arena& arena);

// §6.23 (printed page 138): the self-determined type of `expr`, which a type
// reference to the expression stands for, the expression left unevaluated.
// - A name is the type its declaration writes; a bit-select or part-select of
//   a vector is unsigned and of the vector's state (§11.5.1), one bit or as
//   many as it names; an element of a packed array is the array's element
//   type, unsigned unless that is a name (§7.4.1); an element of an unpacked
//   array the array's element type (§7.4.2); a character of a string a byte
//   (§6.16); a member of a structure or union the type it is declared with
//   (§7.2); and a property read through a class handle the type the class
//   declares it with (§8.5).
// - A call of a function is the type the function returns (§13.4.1), as is
//   one of a class's method through a handle (§8.6), and a
//   call of a built-in method the type its clause gives the result: a
//   string's (§6.16), an enumeration's (§6.19.5), a dynamic array's, a
//   queue's or an associative array's (§7.5.2, §7.9, §7.10.2), or an array
//   reduction's (§7.12.3), the element's type or its with clause's; a cast
//   the type it names, a signing cast its operand re-signed and a size cast
//   its operand's signing and state at the size it names (§6.24.1); a system
//   function the type its clause gives the result (system_function_types.h),
//   $signed and $unsigned their argument re-signed (§11.7).
// - An integer literal is as wide as its size, 32 bits unsized, signed where
//   it is decimal or carries the s designator, and 4-state (§5.7.1); an
//   unbased unsized literal one 4-state bit; a real or time literal real
//   (§5.7.2, §5.8); a string literal eight unsigned 4-state bits a character
//   (§5.9).
// - An increment, a decrement and an assignment are the type of the operand
//   they change (§11.4.2, §11.3.6).
// - An operator is sized and signed as §11.6.1 and §11.8.1 have it, 4-state
//   where an operand is (§11.3.4), and real where an operand is real, or
//   shortreal where one is shortreal and none real (§11.3.1); a relational,
//   equality, logical, reduction or set membership operator is one unsigned
//   bit, and a concatenation and a replication are unsigned (§11.4.12).
// The type made for an operation is a VectorType.
// Nothing for an expression whose type no data type alone carries -- an
// unpacked array -- for an element of a dynamic object,
// which §6.23 forbids the expression to reference, for a method that gives no
// value, and for one written with a name the scope does not resolve.
std::optional<DataType> ExprSelfType(const Expr* expr,
                                     const ExprTypeScope& scope);

// §6.23 with §7.4: the self-determined type of `expr` as ExprSelfType gives
// it, or the unpacked array type of an expression that is an unpacked array:
// a name declared with unpacked dimensions, as many as the declaration
// records; an element of a multidimensional array, its dimensions after the
// first (§7.4.5); and an array locator method's call, a queue (§7.12.1) of the
// array's element type for find, find_first, find_last, min, max and unique,
// and of int, or an associative array's index type, for find_index,
// find_first_index, find_last_index and unique_index. A typedef name the type
// is written with is left as written. Nothing for a slice, whose type's bounds
// §6.22.1(f) would match by are not stated, and where ExprSelfType gives
// nothing.
std::optional<UnpackedArrayType> ExprSelfArrayType(const Expr* expr,
                                                   const ExprTypeScope& scope);

// The unpacked array type of `value`: its type under its unpacked dimensions,
// nothing where those are not recorded.
std::optional<UnpackedArrayType> ValueArrayType(const DeclaredValue& value);

}  // namespace delta
