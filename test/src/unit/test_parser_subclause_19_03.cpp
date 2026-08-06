#include "fixture_parser.h"
#include "fixture_program.h"

using namespace delta;

namespace {

TEST_F(VerifyParseTest, BasicCovergroup) {
  auto* unit = Parse(R"(
    module m;
      covergroup cg @(posedge clk);
        coverpoint x;
      endgroup
    endmodule
  )");
  ASSERT_EQ(unit->modules.size(), 1u);
}

TEST_F(VerifyParseTest, CovergroupEndLabel) {
  auto* unit = Parse(R"(
    module m;
      covergroup my_cg @(posedge clk);
        coverpoint x;
      endgroup : my_cg
    endmodule
  )");
  ASSERT_EQ(unit->modules.size(), 1u);
}

// LRM 19.3: a coverage_event may be a block event expression introduced with
// @@, naming a begin/end of a hierarchical block, task, function, or method.
TEST(CovergroupParsing, CovergroupWithBlockEvent) {
  EXPECT_TRUE(ParseOk(R"(
    module m;
      covergroup cg @@(begin top.worker);
        coverpoint x;
      endgroup
    endmodule
  )"));
}

// LRM 19.3: a coverage_event may be a sample() method with customized
// arguments via "with function sample".
TEST(CovergroupParsing, CovergroupWithFunctionSample) {
  EXPECT_TRUE(ParseOk(R"(
    module m;
      covergroup cg with function sample(int v);
        coverpoint v;
      endgroup
    endmodule
  )"));
}

// LRM 19.3: a covergroup can be defined in a class. This is the construct
// shared with LRM 8.3, where class_item admits a covergroup_declaration.
TEST(CovergroupParsing, CovergroupDefinedInClass) {
  EXPECT_TRUE(ParseOk(R"(
    class C;
      logic [2:0] addr;
      covergroup cg @(addr);
        coverpoint addr;
      endgroup
    endclass
  )"));
}

// LRM 19.3: the coverage_event is optional; with no event specified the
// covergroup relies on a default sample() method, so the header may end right
// after the covergroup name.
TEST(CovergroupParsing, CovergroupWithNoCoverageEvent) {
  EXPECT_TRUE(ParseOk(R"(
    module m;
      covergroup cg;
        coverpoint x;
      endgroup
    endmodule
  )"));
}

// LRM 19.3 (footnote 29): the extends form of a covergroup is written inside a
// class.
TEST(CovergroupParsing, CovergroupExtendsInClass) {
  EXPECT_TRUE(ParseOk(R"(
    class C;
      covergroup cg extends base_cg;
        coverpoint x;
      endgroup
    endclass
  )"));
}

// LRM 19.3: a covergroup can be defined in a package.
TEST(CovergroupParsing, CovergroupInPackage) {
  EXPECT_TRUE(ParseOk(R"(
    package p;
      covergroup cg @(posedge clk);
        coverpoint x;
      endgroup
    endpackage
  )"));
}

// LRM 19.3: a covergroup can be defined in a program.
TEST(CovergroupParsing, CovergroupInProgram) {
  EXPECT_TRUE(ParseOk(R"(
    program prog;
      covergroup cg @(posedge clk);
        coverpoint x;
      endgroup
    endprogram
  )"));
}

// LRM 19.3: a covergroup may declare an optional list of formal arguments.
TEST(CovergroupParsing, CovergroupWithFormalArguments) {
  EXPECT_TRUE(ParseOk(R"(
    module m;
      covergroup cg (ref int x, input int c) @(posedge clk);
        coverpoint x;
      endgroup
    endmodule
  )"));
}

// LRM 19.3: a covergroup specification can include coverage options.
TEST(CovergroupParsing, CovergroupWithCoverageOption) {
  EXPECT_TRUE(ParseOk(R"(
    module m;
      covergroup cg @(posedge clk);
        option.per_instance = 1;
        coverpoint x;
      endgroup
    endmodule
  )"));
}

// LRM 19.3: an output formal argument is illegal for a covergroup.
TEST(CovergroupParsing, OutputFormalArgumentRejected) {
  EXPECT_FALSE(ParseOk(R"(
    module m;
      covergroup cg (output int x) @(posedge clk);
        coverpoint x;
      endgroup
    endmodule
  )"));
}

// LRM 19.3: an inout formal argument is illegal for a covergroup.
TEST(CovergroupParsing, InoutFormalArgumentRejected) {
  EXPECT_FALSE(ParseOk(R"(
    module m;
      covergroup cg (inout int x) @(posedge clk);
        coverpoint x;
      endgroup
    endmodule
  )"));
}

// LRM 19.3: a covergroup can be defined in an interface.
TEST(CovergroupParsing, CovergroupInInterface) {
  EXPECT_TRUE(ParseOk(R"(
    interface intf;
      logic [2:0] addr;
      covergroup cg @(addr);
        coverpoint addr;
      endgroup
    endinterface
  )"));
}

// LRM 19.3: a covergroup can be defined in a checker.
TEST(CovergroupParsing, CovergroupInChecker) {
  EXPECT_TRUE(ParseOk(R"(
    checker chk;
      covergroup cg @(posedge clk);
        coverpoint x;
      endgroup
    endchecker
  )"));
}

// LRM 19.3: coverage_option has a second alternative,
// "type_option . member = constant_expression", distinct from the
// "option . member = expression" form.
TEST(CovergroupParsing, CovergroupWithTypeOption) {
  EXPECT_TRUE(ParseOk(R"(
    module m;
      covergroup cg @(posedge clk);
        type_option.merge_instances = 1;
        coverpoint x;
      endgroup
    endmodule
  )"));
}

// LRM 19.3: coverage_spec has two alternatives, cover_point and cover_cross.
// This exercises the cover_cross alternative, matching the shape of the g2
// example (two coverage points crossed under a label).
TEST(CovergroupParsing, CovergroupWithCrossCoverage) {
  EXPECT_TRUE(ParseOk(R"(
    module m;
      covergroup cg @(posedge clk);
        cp_a: coverpoint a;
        cp_b: coverpoint b;
        axb: cross cp_a, cp_b;
      endgroup
    endmodule
  )"));
}

// LRM 19.3: block_event_expression is recursively defined so that two block
// events may be combined with "or"; the coverage sample is then triggered by
// either event.
TEST(CovergroupParsing, CovergroupWithOredBlockEvents) {
  EXPECT_TRUE(ParseOk(R"(
    module m;
      covergroup cg @@(begin top.worker or end top.worker);
        coverpoint x;
      endgroup
    endmodule
  )"));
}

// LRM 19.3: a block event expression has two keyword forms, "begin" and "end".
// The "end" form triggers the sample after the named block finishes; this
// exercises that alternative on its own.
TEST(CovergroupParsing, CovergroupWithEndBlockEvent) {
  EXPECT_TRUE(ParseOk(R"(
    module m;
      covergroup cg @@(end top.worker);
        coverpoint x;
      endgroup
    endmodule
  )"));
}

// LRM 19.3 (negative form of the block event grammar): a block event
// expression must open with either "begin" or "end"; a bare hierarchical name
// with no keyword is illegal.
TEST(CovergroupParsing, CovergroupBlockEventMissingBeginEndRejected) {
  EXPECT_FALSE(ParseOk(R"(
    module m;
      covergroup cg @@(top.worker);
        coverpoint x;
      endgroup
    endmodule
  )"));
}

// LRM 19.3 (negative form of the with-function coverage_event): the customized
// sampling method introduced by "with function" must name the sample method;
// any other function name is illegal.
TEST(CovergroupParsing, CovergroupWithFunctionNonSampleRejected) {
  EXPECT_FALSE(ParseOk(R"(
    module m;
      covergroup cg with function collect(int v);
        coverpoint v;
      endgroup
    endmodule
  )"));
}

}  // namespace
