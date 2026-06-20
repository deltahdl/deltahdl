#include "fixture_parser.h"
#include "helpers_assoc_array_index_dim.h"

using namespace delta;

namespace {

TEST(UserDefinedTypeAssocArrayParsing, TypedefIndexParsed) {
  ExpectAssocArrayIdentifierIndexDim(
      "module t;\n"
      "  typedef bit [3:0] nibble_t;\n"
      "  int aa[nibble_t];\n"
      "endmodule\n",
      "aa", "nibble_t");
}

}  // namespace
