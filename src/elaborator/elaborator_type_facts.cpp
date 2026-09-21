#include "elaborator/elaborator_type_facts.h"

#include <cstddef>
#include <cstdint>
#include <optional>
#include <string_view>

#include "common/arena.h"
#include "common/packed_range.h"
#include "elaborator/const_eval.h"
#include "elaborator/type_eval.h"
#include "parser/ast_type.h"

namespace delta {

// §6.18's "type the name stands for", following a chain of typedefs to the kind
// at its end. The walk is bounded by the table's own size so a table that names
// itself -- which the elaborator reports elsewhere rather than resolving --
// cannot spin here.
static const DataType& ResolvedType(const DataType& dtype,
                                    const TypedefMap& typedefs) {
  const DataType* cur = &dtype;
  for (size_t steps = 0; steps <= typedefs.size(); ++steps) {
    if (cur->kind != DataTypeKind::kNamed) return *cur;
    auto it = typedefs.find(cur->type_name);
    if (it == typedefs.end()) return *cur;
    cur = &it->second;
  }
  return *cur;
}

static DataTypeKind ResolvedTypeKind(const DataType& dtype,
                                     const TypedefMap& typedefs) {
  return ResolvedType(dtype, typedefs).kind;
}

// §11.5.1 has the bit an index addresses decided in part by the declaration,
// and §6.18 makes a typedef name's declaration the type it stands for: this is
// the packed range a name stands for, read off the type at the end of its
// chain of names, for a type declared with one packed dimension whose bounds
// fold. A name written with a dimension of its own, `typedef bsix [1:10]
// v5_t`, stacks that dimension on the type it names (§7.4.4) and addresses
// elements rather than bits, as does a type with more than one packed
// dimension (§7.4.1); neither is a range of bits an index resolves against, so
// neither records one and a variable of such a type keeps the [width-1:0] view
// it had.
static std::optional<PackedRange> TypeNameRange(const DataType& dtype,
                                                const TypedefMap& typedefs) {
  if (dtype.kind == DataTypeKind::kNamed && dtype.packed_dim_left != nullptr)
    return std::nullopt;
  const DataType& end = ResolvedType(dtype, typedefs);
  if (end.kind == DataTypeKind::kNamed || end.packed_dim_left == nullptr ||
      end.packed_dim_right == nullptr || !end.extra_packed_dims.empty()) {
    return std::nullopt;
  }
  auto left = ConstEvalInt(end.packed_dim_left);
  auto right = ConstEvalInt(end.packed_dim_right);
  if (!left || !right) return std::nullopt;
  return PackedRange{*left, *right};
}

// The width the table records for one name. §8.27's forward class declaration
// leaves the type it introduces implicit -- `typedef class C;` records C with
// nothing behind it until the class itself is declared -- and §6.10's answer
// for an implicit type is one bit, which is not what a class is: §8.3 makes a
// class variable a handle to an object. Recording that 1 made a class name's
// width turn on whether the design happened to forward-declare it, since
// without the forward declaration the name is in no typedef map at all and the
// table answers 0. 0 is what it answers for the forward-declared one too.
static uint32_t TypeNameWidth(const DataType& dtype, const TypedefMap& typedefs,
                              bool is_aggregate) {
  if (is_aggregate || dtype.kind == DataTypeKind::kImplicit) return 0;
  return EvalTypeWidth(dtype, typedefs);
}

// §6.18: what a name stands for is the whole of the type it was declared with,
// dimensions included, and the map carries only the element type -- the parser
// leaves a typedef's unpacked dimensions on the declaration rather than in the
// data type. So a name declared as an unpacked array, dynamic array, queue or
// associative array would be recorded at one element's width, which nothing
// downstream can tell from the width of a singular type: `typedef int arr_t[4]`
// answered 32, exactly as `typedef int i_t` does, and a formal or local written
// with it was sized to one element. 0 is what the table says instead, since
// that is what every reader already treats as "no width the type declares" and
// falls back from. The whole aggregate's bit count is a different claim and not
// one an unpacked array has at all (§7.4).
//
// §7.2.1's layout is the fourth fact, and it is recorded for the names that
// have one: a typedef standing for a packed struct or union. The copy is taken
// into the arena, with its nested aggregate members resolved the way a
// variable's declaration resolves them, because the typedef table it is read
// from belongs to the elaborator and is gone by the time a run reads a member
// out of a value held under the name.
void PopulateTypeWidths(const TypeNameSources& src, TypeNameFacts& out) {
  for (const auto& [name, dtype] : src.typedefs) {
    out.widths[name] =
        TypeNameWidth(dtype, src.typedefs, src.aggregates.count(name) > 0);
    out.kinds[name] = ResolvedTypeKind(dtype, src.typedefs);
    out.is_signed[name] = IsSignedType(dtype, src.typedefs);
    // §8.3: a chain ending in a name the table does not resolve names a
    // class, which the simulator finds through this name.
    const DataType& end = ResolvedType(dtype, src.typedefs);
    if (end.kind == DataTypeKind::kNamed && end.type_name != name) {
      out.targets[name] = end.type_name;
    }
    // §6.19 with §6.18: the enumeration a name stands for, at the end of its
    // chain of typedefs, whose members §6.19.5's methods on a value held
    // under the name walk (RtlirDesign::type_enums).
    if (end.kind == DataTypeKind::kEnum) {
      out.enums[name] = src.arena.Create<DataType>(end);
    }
    if (auto range = TypeNameRange(dtype, src.typedefs)) {
      out.ranges[name] = *range;
    }
    if (dtype.kind != DataTypeKind::kStruct &&
        dtype.kind != DataTypeKind::kUnion) {
      continue;
    }
    auto* copy = src.arena.Create<DataType>(dtype);
    ResolveNestedAggregateTypes(*copy, src.typedefs, src.arena);
    out.layouts[name] = copy;
  }
}

}  // namespace delta
