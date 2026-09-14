#include <gtest/gtest.h>

#include <type_traits>
#include <vector>

#include "parser/ast.h"
#include "simulator/dpi_c_type.h"
#include "simulator/svdpi.h"

using namespace delta;

// Annex H.8.9 (Function result): the type of a function result is
// restricted to byte, shortint, int, longint, real, shortreal, chandle and
// string, and scalar values of type bit and logic, each returned as the C
// type Table H.1 gives it, the encodings of bit and logic being those
// svdpi.h gives (§H.10.1.1). The cases check the list of result types and
// the C type each is returned as, and the scalar encoding.

namespace {

// §H.8.9: the ten result types in the clause's order, each with a C type
// to be returned as, where an integer, a time, a packed array's kind under
// a width and a struct are not among them.
TEST(DpiCFunctionResult, TheResultTypesAreTheTenTheClauseLists) {
  const std::vector<DataTypeKind> kExpected = {
      DataTypeKind::kByte,    DataTypeKind::kShortint, DataTypeKind::kInt,
      DataTypeKind::kLongint, DataTypeKind::kReal,     DataTypeKind::kShortreal,
      DataTypeKind::kChandle, DataTypeKind::kString,   DataTypeKind::kBit,
      DataTypeKind::kLogic};
  EXPECT_EQ(DpiResultTypes(), kExpected);
  for (const DataTypeKind kKind : DpiResultTypes()) {
    EXPECT_TRUE(DpiTypeMayBeAResult(kKind));
    EXPECT_FALSE(DpiCTypeOfResult(kKind).empty());
  }
  EXPECT_FALSE(DpiTypeMayBeAResult(DataTypeKind::kInteger));
  EXPECT_FALSE(DpiTypeMayBeAResult(DataTypeKind::kTime));
  EXPECT_FALSE(DpiTypeMayBeAResult(DataTypeKind::kStruct));
  EXPECT_FALSE(DpiTypeMayBeAResult(DataTypeKind::kEvent));
}

// §H.8.9 with Table H.1: each result type is returned as its C type --
// char, short int, int, long long, double, float, void*, const char* --
// and a scalar bit or logic as svBit or svLogic, the unsigned char of
// svdpi.h whose codes are sv_0, sv_1, sv_z and sv_x.
TEST(DpiCFunctionResult, EachResultIsReturnedAsItsTableType) {
  EXPECT_EQ(DpiCTypeOfResult(DataTypeKind::kByte), "char");
  EXPECT_EQ(DpiCTypeOfResult(DataTypeKind::kShortint), "short int");
  EXPECT_EQ(DpiCTypeOfResult(DataTypeKind::kLongint), "long long");
  EXPECT_EQ(DpiCTypeOfResult(DataTypeKind::kShortreal), "float");
  EXPECT_EQ(DpiCTypeOfResult(DataTypeKind::kChandle), "void*");
  EXPECT_EQ(DpiCTypeOfResult(DataTypeKind::kString), "const char*");
  EXPECT_EQ(DpiCTypeOfResult(DataTypeKind::kBit), "svBit");
  EXPECT_EQ(DpiCTypeOfResult(DataTypeKind::kLogic), "svLogic");
  EXPECT_TRUE((std::is_same<svBit, unsigned char>::value));
  EXPECT_TRUE((std::is_same<svLogic, unsigned char>::value));
  const svLogic kCodes[] = {sv_0, sv_1, sv_z, sv_x};
  EXPECT_EQ(kCodes[0], 0);
  EXPECT_EQ(kCodes[3], 3);
}

}  // namespace
