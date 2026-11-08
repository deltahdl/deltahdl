#ifndef DELTA_ELABORATOR_COVERPOINT_BIN_SET_EXPRESSION_H
#define DELTA_ELABORATOR_COVERPOINT_BIN_SET_EXPRESSION_H

#include <cstdint>

namespace delta {

struct DataType;

bool SetExpressionElementTypeAllowed(const DataType& coverpoint_type,
                                     const DataType& element_type);

enum class SetExpressionArrayKind : uint8_t {
  kFixedSize,
  kDynamic,
  kQueue,
  kAssociative,
};

bool SetExpressionArrayKindAllowed(SetExpressionArrayKind kind);

enum class SetExpressionNameOrigin : uint8_t {
  kCoverpointIdentifier,
  kBinIdentifier,
  kExternal,
};

bool SetExpressionNameVisible(SetExpressionNameOrigin origin);

}  // namespace delta

#endif
