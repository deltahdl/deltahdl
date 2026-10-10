#pragma once

#include <string_view>
#include <unordered_map>
#include <unordered_set>
#include <vector>

#include "common/diagnostic.h"
#include "common/source_loc.h"
#include "elaborator/type_eval.h"

namespace delta {

struct DataType;
struct Expr;

// What a judgement of a net's data type reads besides the typedefs: the
// unpacked dimensions each typedef wrote, which a TypedefMap entry does not
// carry, and the class names, which a data type or an associative index may
// name without being a typedef.
struct TypeShapeTables {
  const TypedefMap& typedefs;
  const std::unordered_map<std::string_view, std::vector<Expr*>>& typedef_dims;
  const std::unordered_set<std::string_view>& class_names;
};

// The type `dtype` stands for once every typedef name it is written with has
// been followed, or null when a name resolves to nothing in `typedefs` or the
// names run in a cycle. Each name followed is appended to `names`, so a caller
// can ask what each one wrote besides the type.
const DataType* FollowTypedefs(const DataType& dtype,
                               const TypedefMap& typedefs,
                               std::vector<std::string_view>& names);

// §7.4 (printed page 153): whether the unpacked dimension `dim` is a constant
// range or size. The parser keeps a dynamic array's `[]` as a null dimension,
// a queue's `[$]` and `[$:N]` and the wildcard `[*]` as identifiers of that
// text, and an associative index as the identifier of its index type, which is
// a keyword or the name of a typedef or a class.
bool IsFixedSizeUnpackedDim(const Expr* dim, const TypeShapeTables& tables);

// Syntax 6-2 (printed page 102): a net declarator takes unpacked_dimension, a
// constant range or size, where a variable declarator takes
// variable_dimension. Reports each dimension of `dims`, the ones written after
// the net's name, that is not fixed-size. A net of a user-defined nettype is
// declared through the same net_decl_assignment, so this holds for it too.
void ValidateNetDeclaratorDims(const std::vector<Expr*>& dims,
                               const TypeShapeTables& tables, DiagEngine& diag,
                               SourceLoc loc);

// §6.7.1 (printed page 103) restricts a net's data type to a) a 4-state
// integral type or b) a fixed-size unpacked array, structure or union each of
// whose elements has a valid net data type. Reports `dtype` at `loc` when it is
// not one of those, judging a typedef name as what it stands for and a member
// as its own type. Shared because a net is not only what a net declaration
// produces: §23.2.2.3 makes a port with the port kind omitted a net too, and
// the rule that decides what such a thing may carry is one rule wherever the
// net came from.
void ValidateNetDataTypeIs4State(const DataType& dtype,
                                 const TypedefMap& typedefs, DiagEngine& diag,
                                 SourceLoc loc);

// §6.7.1 item b: a typedef carries its unpacked dimensions into the type it
// names, so a net declared through one is an array of that shape, and the
// array has to be fixed-size. Reports `dtype` at `loc` when a typedef name it
// is written with, or one that name leads to, wrote a dimension that is not.
void ValidateNetTypedefDims(const DataType& dtype,
                            const TypeShapeTables& tables, DiagEngine& diag,
                            SourceLoc loc);

// §6.6.7 (printed pages 97–98): the data type of a user-defined nettype shall
// be a 4-state or 2-state integral type, `real` or `shortreal`, or a fixed-size
// unpacked array, structure or union each of whose elements is one of these.
// Judges `dtype` as the type its typedef names stand for, so a typedef of a
// string or a class is no more legal than the type written out. A name that
// resolves to nothing in `tables` leaves nothing to judge and is accepted.
bool IsLegalNettypeDataType(const DataType& dtype,
                            const TypeShapeTables& tables);

}  // namespace delta
