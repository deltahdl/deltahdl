// §6.8

#include "elaboration/type_eval.h"
#include "parser/ast.h"
#include <gtest/gtest.h>

using namespace delta;

namespace {

TEST(TypeEval, ImplicitlySignedTypes) {
  // §6.8: integer, int, shortint, longint, byte are implicitly signed.
  // logic, reg, bit are NOT implicitly signed.
  struct Case {
    DataTypeKind kind;
    bool expected;
    const char *label;
  };
  const Case kCases[] = {
      {DataTypeKind::kInteger, true, "integer"},
      {DataTypeKind::kInt, true, "int"},
      {DataTypeKind::kShortint, true, "shortint"},
      {DataTypeKind::kLongint, true, "longint"},
      {DataTypeKind::kByte, true, "byte"},
      {DataTypeKind::kLogic, false, "logic"},
      {DataTypeKind::kReg, false, "reg"},
      {DataTypeKind::kBit, false, "bit"},
  };
  for (const auto &c : kCases) {
    EXPECT_EQ(IsImplicitlySigned(c.kind), c.expected) << c.label;
  }
}

} // namespace
