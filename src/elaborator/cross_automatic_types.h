#ifndef DELTA_ELABORATOR_CROSS_AUTOMATIC_TYPES_H
#define DELTA_ELABORATOR_CROSS_AUTOMATIC_TYPES_H

#include <cstdint>
#include <string>
#include <string_view>
#include <vector>

namespace delta {

// §19.6.1.3 "Cross bin automatically defined types". A cross defines a coverage
// space of value tuples; to describe the structure of that space SystemVerilog
// provides two automatically defined types in every cross, named CrossValType
// and CrossQueueType. These helpers carry the §19.6.1.3 rules that the
// elaborator applies when it materializes those implicit types: how the struct
// is shaped from the cross's coverpoints, how the queue wraps it, and how the
// names are scoped to the cross body. The cross grammar itself (cover_cross,
// list_of_cross_items, ...) belongs to §19.6's Syntax 19-4, not here.

// Canonical names of the two automatically defined cross types. Their scope is
// the cross itself (see CrossAutoTypeIsVisible).
inline constexpr std::string_view kCrossValTypeName = "CrossValType";
inline constexpr std::string_view kCrossQueueTypeName = "CrossQueueType";

// §19.6.1.3: CrossValType is a struct with one member per coverpoint in the
// cross. The name and type of each field are the name and type of the
// corresponding coverpoint. This describes a single such member.
struct CrossValMember {
  std::string name;  // field name = corresponding coverpoint's name
  std::string type;  // field type = corresponding coverpoint's type
};

// The CrossValType struct definition for one cross: one member per coverpoint,
// in coverpoint order.
struct CrossValTypeDef {
  std::vector<CrossValMember> members;
};

// §19.6.1.3: CrossQueueType is an unbounded queue of CrossValType elements.
struct CrossQueueTypeDef {
  std::string_view element_type = kCrossValTypeName;
  bool unbounded = true;
};

// §19.6.1.3: build the CrossValType struct for a cross from its coverpoints,
// preserving one member per coverpoint, each carrying the coverpoint's name and
// type, in declaration order.
CrossValTypeDef BuildCrossValType(
    const std::vector<CrossValMember>& coverpoints);

// §19.6.1.3: build the CrossQueueType for a cross — an unbounded queue whose
// element type is CrossValType.
CrossQueueTypeDef BuildCrossQueueType();

// §19.6.1.3: when the range bounds for a coverpoint's type are not evident
// (e.g., the coverpoint expression is a concatenation and no other type is
// specified), the field type assumes the bounds
// [$bits(coverpoint_expression)-1:0]. Returns the packed two-state vector type
// string for a coverpoint of the given bit width.
std::string CrossValMemberDefaultBoundType(int64_t expr_bit_width);

// §19.6.1.3: the scope of the automatic type names is the cross itself; the
// types are not accessible outside this scope. Returns true only when the
// querying scope is the cross that defines the types.
bool CrossAutoTypeIsVisible(std::string_view querying_scope,
                            std::string_view defining_cross_scope);

// §19.6.1.3: the cross types shall be considered as implicit typedefs in the
// body of the cross. Returns true when `name` is one of the implicitly declared
// cross type names that the cross body resolves as a typedef.
bool IsImplicitCrossTypedefName(std::string_view name);

}  // namespace delta

#endif  // DELTA_ELABORATOR_CROSS_AUTOMATIC_TYPES_H
