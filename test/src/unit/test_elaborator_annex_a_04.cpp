#include <string>

#include "fixture_elaborator.h"
#include "helpers_reported_error.h"

using namespace delta;

// A.4 "Instantiations" writes no production of its own. It is a heading over
// A.4.1's four instantiation forms and A.4.2's generate constructs, and what it
// has to say is which of those forms are the same form. Three of A.4.1's four
// are: `module_instantiation`, `interface_instantiation` and
// `program_instantiation` each read
//
//     <identifier> [ parameter_value_assignment ]
//     hierarchical_instance { , hierarchical_instance } ;
//
// differing only in the class of identifier that opens them. The fourth is
// written out in full and is narrower --
//
//     checker_instantiation ::=
//         ps_checker_identifier name_of_instance
//         ( [ list_of_checker_port_connections ] ) ;
//
// -- carrying no parameter value assignment. A checker takes its arguments
// through the ports that connection list fills (§17.3).
//
// Each subclause has a file of its own driving the form it writes. These cases
// are the comparison between them, which no one of those files makes: what the
// three admit is refused of the fourth, and the same override written against
// each of the three is what says the refusal is the fourth form's own and not a
// rule about overrides.

namespace {

// A checker's parameter value assignment is not part of the form A.4.1.4
// writes. Read by the path all four instantiations are parsed by, it was taken
// for the other three's and handed to a declaration with no parameter to
// override.
TEST(InstantiationFormElaboration, ACheckerTakesNoParameterValueAssignment) {
  ElabFixture f;
  ElaborateSrc(
      "checker chk(input logic a);\n"
      "endchecker\n"
      "module m;\n"
      "  logic s;\n"
      "  chk #(.W(4)) c1(s);\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(
      f.diag.Diagnostics(),
      "checker 'chk' cannot be instantiated with a parameter value assignment",
      5, "A.4.1.4"));
}

// The ordered form of the same assignment is the same thing written another
// way, and A.4.1.4 leaves out the whole of `parameter_value_assignment` rather
// than one of the two lists `list_of_parameter_value_assignments` offers.
TEST(InstantiationFormElaboration, AnOrderedAssignmentOnACheckerIsRefusedToo) {
  ElabFixture f;
  ElaborateSrc(
      "checker chk(input logic a);\n"
      "endchecker\n"
      "module m;\n"
      "  logic s;\n"
      "  chk #(4) c1(s);\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(
      f.diag.Diagnostics(),
      "checker 'chk' cannot be instantiated with a parameter value assignment",
      5, "A.4.1.4"));
}

// And the checker instantiation that stays inside its own form elaborates: the
// refusal is of the parameter value assignment and not of the instantiation.
TEST(InstantiationFormElaboration, ACheckerWithoutOneElaborates) {
  ElabFixture f;
  auto* design = Elaborate(
      "checker chk(input logic a);\n"
      "endchecker\n"
      "module m;\n"
      "  logic s;\n"
      "  chk c1(s);\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

// The three forms that do write `[ parameter_value_assignment ]` keep it. The
// same override that the checker refuses is what a module, an interface and a
// program instantiation are each written to take, which is what makes the
// refusal above a fact about A.4.1.4's form rather than about overrides.
TEST(InstantiationFormElaboration, TheOtherThreeFormsTakeTheAssignment) {
  ElabFixture f;
  auto* design = Elaborate(
      "interface ifc #(parameter W = 1) ();\n"
      "endinterface\n"
      "program prg #(parameter W = 1) ();\n"
      "endprogram\n"
      "module sub #(parameter W = 1) ();\n"
      "endmodule\n"
      "module m;\n"
      "  ifc #(.W(4)) i1();\n"
      "  prg #(.W(4)) p1();\n"
      "  sub #(.W(4)) s1();\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

// A.4.1.4 writes one name_of_instance where the other three forms write
// `hierarchical_instance { , hierarchical_instance }`. Read by the shared path,
// `chk c1(s), c2(t);` was two instances of the checker; the second is now
// reported, and the first stands.
TEST(InstantiationFormElaboration, ACheckerTakesOneInstancePerInstantiation) {
  ElabFixture f;
  ElaborateSrc(
      "checker chk(input logic a);\n"
      "endchecker\n"
      "module m;\n"
      "  logic s, t;\n"
      "  chk c1(s), c2(t);\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "checker 'chk' is instantiated one instance to an "
                            "instantiation; 'c2' after a ',' is a second",
                            5, "A.4.1.4"));
  EXPECT_FALSE(ReportedError(f.diag.Diagnostics(),
                             "'c1' after a ',' is a second", 5, "A.4.1.4"));
}

// The three forms that do write the list keep it: two instances to one
// instantiation of a module, an interface and a program elaborate.
TEST(InstantiationFormElaboration, TheOtherThreeFormsTakeTheInstanceList) {
  ElabFixture f;
  auto* design = Elaborate(
      "interface ifc ();\n"
      "endinterface\n"
      "program prg ();\n"
      "endprogram\n"
      "module sub ();\n"
      "endmodule\n"
      "module m;\n"
      "  ifc i1(), i2();\n"
      "  prg p1(), p2();\n"
      "  sub s1(), s2();\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

}  // namespace
