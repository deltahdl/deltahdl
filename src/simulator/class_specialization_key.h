#pragma once

#include <cstddef>
#include <string>

namespace delta {

class SimContext;
struct ClassDecl;
struct DataType;

// §8.25 with §23.10.2.2: a type parameter's actual matches by matching types,
// so the key has to tell two actuals apart exactly when their types differ. A
// named type is told by its name. A built-in one is spelled as §6.22.1 matches
// it (IntegralTypeKey), whatever name it carries: ParseDataType
// (parser_types.cpp) records a keyword's own text as the name of the type a
// declaration writes, while the same keyword read out of a scope form's list
// (TypeSpelledBy) carries no name at all, so a name taken first keyed a
// declaration's `C #(byte)` and the scope form `C#(byte)::` as two
// specializations of one type. The declaration's own default stands where the
// specialization leaves the parameter out, which is the type the default
// specialization binds.
//
// §6.22.1 also makes a typedef name match the type it stands for, so a name
// reaching a built-in type through its chain of typedefs (BuiltinTypedefTarget)
// is spelled as that type is: keyed by the alias's own name, `S #(word_t)`
// under `typedef int word_t;` was a specialization apart from `S #(int)`, with
// statics of its own. Keyed by keyword and width, `C #(bit signed [7:0])` was
// apart from `C #(byte)`, and `C #(bit [2:0])` one with `C #(bit [3:1])`. A
// built-in type that is not integral is spelled by its keyword, realtime as
// real, the two being one type (§6.12, printed page 110).
std::string TypeActualKey(const ClassDecl* decl, size_t i,
                          const DataType* actual, SimContext& ctx);

}  // namespace delta
