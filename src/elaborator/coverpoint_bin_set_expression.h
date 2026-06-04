#ifndef DELTA_ELABORATOR_COVERPOINT_BIN_SET_EXPRESSION_H
#define DELTA_ELABORATOR_COVERPOINT_BIN_SET_EXPRESSION_H

#include <cstdint>

namespace delta {

struct DataType;

// §19.5.1.2 restricts the set_covergroup_expression that defines a coverpoint
// bin. The set_covergroup_expression production itself belongs to §19.5's
// Syntax 19-2 (footnote 32 only points here); the helpers below carry the
// three compile-time legality rules the text of §19.5.1.2 adds. The runtime
// timing rule of §19.5.1.2 lives in the simulator (see the §19.5.1.2 helper in
// coverage.h).

// §19.5.1.2: the expression may yield any array whose element type is
// assignment compatible with the coverpoint type. Returns true when the array's
// element type can be assigned to the coverpoint type, reusing the §6.22.1
// assignment-compatibility rule. The coverpoint type is the assignment target.
bool SetExpressionElementTypeAllowed(const DataType& coverpoint_type,
                                     const DataType& element_type);

// The kind of array a set_covergroup_expression yields. §19.5.1.2 permits a
// fixed-size, dynamic, or queue array but singles out associative arrays as the
// one exception that is not permitted (see §7.8 for the array kinds).
enum class SetExpressionArrayKind : uint8_t {
  kFixedSize,
  kDynamic,
  kQueue,
  kAssociative,
};

// §19.5.1.2: any array kind is permitted with the exception of associative
// arrays. Returns true for every kind except an associative array.
bool SetExpressionArrayKindAllowed(SetExpressionArrayKind kind);

// Where a name referenced inside a set_covergroup_expression is declared.
// §19.5.1.2 makes identifiers declared within the covergroup invisible to the
// expression, naming coverpoint identifiers and bin identifiers specifically;
// names declared outside the covergroup remain visible.
enum class SetExpressionNameOrigin : uint8_t {
  kCoverpointIdentifier,
  kBinIdentifier,
  kExternal,
};

// §19.5.1.2: identifiers declared within the covergroup (coverpoint identifiers
// and bin identifiers) are not visible within the expression. Returns true only
// for a name declared outside the covergroup.
bool SetExpressionNameVisible(SetExpressionNameOrigin origin);

}  // namespace delta

#endif  // DELTA_ELABORATOR_COVERPOINT_BIN_SET_EXPRESSION_H
