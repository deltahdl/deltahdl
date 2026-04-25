#include "fixture_program.h"
#include "fixture_simulator.h"
#include "helpers_parser_verify.h"

using namespace delta;

namespace {

// §32.9 Syntax 32-1 minimum form: a single sdf_file argument is the
// only required positional argument. The bare-string form is the most
// common spelling and must parse with no surrounding optional
// arguments.
TEST_F(ApiParseTest, SdfAnnotateSystemCall) {
  auto* unit = Parse(R"(
    module m;
      initial $sdf_annotate("timing.sdf");
    endmodule
  )");
  ASSERT_EQ(unit->modules.size(), 1u);
}

// §32.9 Syntax 32-1: every optional argument position from
// module_instance through scale_type is permitted in one invocation.
// A regression that mis-counted the trailing brackets of the
// productions (a real risk given Syntax 32-1's unusual nested
// `[ , [ ... ] ]` shape) would reject this form even though each
// individual argument is well-formed.
TEST_F(ApiParseTest, SdfAnnotateAllSevenArgumentsParse) {
  auto* unit = Parse(R"(
    module top;
      sub u1();
      initial $sdf_annotate("timing.sdf", u1, "cfg.cfg", "annot.log",
                            "MAXIMUM", "1.0:1.0:1.0", "FROM_MTM");
    endmodule
    module sub; endmodule
  )");
  ASSERT_NE(unit, nullptr);
  EXPECT_FALSE(diag_.HasErrors());
}

// §32.9 module_instance paragraph: "Array indices are permitted." A
// scope expression naming an indexed instance — `u1[3]` — must parse
// in the module_instance position. Without explicit coverage, an
// expression parser that only accepts simple identifiers in this
// slot would still pass the bare-string smoke test above.
TEST_F(ApiParseTest, SdfAnnotateAcceptsArrayIndexedScope) {
  auto* unit = Parse(R"(
    module top;
      sub u1[7:0]();
      initial $sdf_annotate("timing.sdf", u1[3]);
    endmodule
    module sub; endmodule
  )");
  ASSERT_NE(unit, nullptr);
  EXPECT_FALSE(diag_.HasErrors());
}

// §32.9 module_instance paragraph: the scope is "the hierarchy level
// of the specified instance", so a hierarchical reference like
// `top.dut` must parse in the module_instance position. The
// bare-identifier form is covered by the all-arguments test above;
// this one specifically pins down the dotted-name form so an
// expression parser that only accepts simple identifiers in this
// slot is caught.
TEST_F(ApiParseTest, SdfAnnotateAcceptsHierarchicalScope) {
  auto* unit = Parse(R"(
    module top;
      sub dut();
      initial $sdf_annotate("timing.sdf", top.dut);
    endmodule
    module sub; endmodule
  )");
  ASSERT_NE(unit, nullptr);
  EXPECT_FALSE(diag_.HasErrors());
}

// §32.9 sdf_file paragraph: the argument is "an expression that is a
// string literal, string data type, or an integral data type
// containing a character string". The string-literal case is the
// minimum-form test above; this one pins down the string-data-type
// case so an expression parser that special-cased only literals in
// the first arg slot would fail here.
TEST_F(ApiParseTest, SdfAnnotateAcceptsStringDataTypeAsSdfFile) {
  auto* unit = Parse(R"(
    module m;
      string filename;
      initial begin
        filename = "timing.sdf";
        $sdf_annotate(filename);
      end
    endmodule
  )");
  ASSERT_NE(unit, nullptr);
  EXPECT_FALSE(diag_.HasErrors());
}

// §32.9 sdf_file paragraph: the third sdf_file form is "an integral
// data type containing a character string". A SystemVerilog packed
// vector wide enough to hold the filename's characters falls under
// this case. Parsing must accept the integral expression in the
// first arg slot exactly as it does for the string-literal and
// string-variable forms.
TEST_F(ApiParseTest, SdfAnnotateAcceptsIntegralDataTypeAsSdfFile) {
  auto* unit = Parse(R"(
    module m;
      bit [8*16-1:0] packed_filename;
      initial begin
        packed_filename = "timing.sdf";
        $sdf_annotate(packed_filename);
      end
    endmodule
  )");
  ASSERT_NE(unit, nullptr);
  EXPECT_FALSE(diag_.HasErrors());
}

// §32.9 Syntax 32-1: the optional arguments are individually
// optional, not all-or-nothing. A caller that only wants to set
// scale_factors must be able to omit module_instance, config_file,
// log_file, and mtm_spec by leaving those positions empty. The
// nested-bracket grammar admits empty positions via successive
// commas; without coverage, a parser that required every leading
// optional to be supplied before reaching scale_factors would
// silently reject this form.
TEST_F(ApiParseTest, SdfAnnotateAcceptsOmittedLeadingOptionals) {
  auto* unit = Parse(R"(
    module m;
      initial $sdf_annotate("timing.sdf", , , , , "1.0:1.0:1.0");
    endmodule
  )");
  ASSERT_NE(unit, nullptr);
  EXPECT_FALSE(diag_.HasErrors());
}

}  // namespace
