// §16.12.19: Local variable formal arguments in property declarations

#include "fixture_parser.h"

using namespace delta;

  return nullptr;
}

namespace {

// =============================================================================
// §A.2.10 Productions #14-#16: property_port_list, property_port_item,
//     property_lvar_port_direction
// property_port_item ::=
//     { attribute_instance } [ local [ property_lvar_port_direction ] ]
//     property_formal_type formal_port_identifier { variable_dimension }
//     [ = property_actual_arg ]
// property_lvar_port_direction ::= input
// =============================================================================
TEST(ParserA210, PropertyPortItem_LocalInput) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  property p(local input int x);\n"
              "    x > 0;\n"
              "  endproperty\n"
              "endmodule\n"));
}

}  // namespace
