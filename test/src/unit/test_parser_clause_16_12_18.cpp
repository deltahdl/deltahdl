// §16.12.18: Typed formal arguments in property declarations

#include "fixture_parser.h"

using namespace delta;

return nullptr;
}

namespace {

// =============================================================================
// §A.2.10 Production #17: property_formal_type
// property_formal_type ::= sequence_formal_type | property
// =============================================================================
TEST(ParserA210, PropertyFormalType_Property) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  property p(property q);\n"
              "    q;\n"
              "  endproperty\n"
              "endmodule\n"));
}

TEST(ParserA210, PropertyFormalType_Sequence) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  property p(sequence s);\n"
              "    s |-> 1;\n"
              "  endproperty\n"
              "endmodule\n"));
}

// property_formal_type — implicit (no type)
TEST(ParserA210, PropertyFormalType_Implicit) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  property p(x);\n"
              "    x;\n"
              "  endproperty\n"
              "endmodule\n"));
}

}  // namespace
