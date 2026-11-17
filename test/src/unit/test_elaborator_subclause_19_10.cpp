#include <gtest/gtest.h>

#include <cstdint>
#include <initializer_list>
#include <string>
#include <tuple>

#include "fixture_elaborator.h"
#include "helpers_reported_error.h"

using namespace delta;

namespace {

using MemberError = std::tuple<uint32_t, const char*, const char*>;

void ExpectNoMemberErrors(const std::string& src,
                          std::initializer_list<MemberError> errors) {
  ElabFixture f;
  ElaborateSrc(src, f);
  for (auto [line, structure, member] : errors) {
    EXPECT_TRUE(ReportedError(
        f.diag.Diagnostics(),
        std::string(structure) + " has no member '" + member + "'", line,
        "19.10"))
        << structure << "." << member << " at line " << line;
  }
  EXPECT_EQ(f.diag.ErrorCount(), errors.size());
}

void ExpectAccepted(const std::string& src) {
  ElabFixture f;
  ElaborateSrc(src, f);
  EXPECT_EQ(f.diag.ErrorCount(), 0u);
}

const char kLevels[] =
    "  bit [1:0] a, b;\n"
    "  covergroup cg;\n"
    "    cp: coverpoint a;\n"
    "    cq: coverpoint b;\n"
    "    x: cross cp, cq;\n"
    "  endgroup\n"
    "  cg c = new;\n";

std::string InModule(const std::string& body) {
  return std::string("module m;\n") + kLevels + body + "endmodule\n";
}

TEST(OptionMembers, NameTheStructureDoesNotDeclareIsError) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  bit [1:0] a;\n"
      "  covergroup cg;\n"
      "    option.foo = 1;\n"
      "    option.strobe = 1;\n"
      "    type_option.at_least = 2;\n"
      "    option.at_least = 2;\n"
      "    type_option.strobe = 1;\n"
      "    coverpoint a { option.bar = 1; }\n"
      "  endgroup\n"
      "  cg c = new;\n"
      "  initial c.option.baz = 2;\n"
      "  initial cg::type_option.qux = 3;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(), "option has no member 'foo'",
                            4, "19.10"));
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "option has no member 'strobe'", 5, "19.10"));
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "type_option has no member 'at_least'", 6,
                            "19.10"));
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(), "option has no member 'bar'",
                            9, "19.10"));
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(), "option has no member 'baz'",
                            12, "19.10"));
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "type_option has no member 'qux'", 13, "19.10"));
  EXPECT_EQ(f.diag.ErrorCount(), 6u);
}

TEST(OptionMembers, UnknownNameInEveryDefinitionLevelIsError) {
  ExpectNoMemberErrors(
      "module m;\n"
      "  bit [1:0] a, b;\n"
      "  covergroup cg;\n"
      "    type_option.foo = 1;\n"
      "    cp: coverpoint a { type_option.zz = 1; }\n"
      "    cq: coverpoint b;\n"
      "    x: cross cp, cq { option.foo = 1; type_option.yy = 1; }\n"
      "  endgroup\n"
      "endmodule\n",
      {{4u, "type_option", "foo"},
       {5u, "type_option", "zz"},
       {7u, "option", "foo"},
       {7u, "type_option", "yy"}});
}

TEST(OptionMembers, EveryLevelsOwnMembersAreAcceptedInItsDefinition) {
  ExpectAccepted(
      "module m;\n"
      "  bit [1:0] a, b;\n"
      "  covergroup cg;\n"
      "    option.name = \"n\";\n"
      "    option.cross_retain_auto_bins = 0;\n"
      "    option.per_instance = 1;\n"
      "    option.get_inst_coverage = 1;\n"
      "    type_option.distribute_first = 1;\n"
      "    type_option.real_interval = 0.5;\n"
      "    cp: coverpoint a { option.goal = 90; option.comment = \"c\";\n"
      "      type_option.real_interval = 0.25; }\n"
      "    cq: coverpoint b;\n"
      "    x: cross cp, cq { option.goal = 80; option.comment = \"d\";\n"
      "      type_option.comment = \"e\"; }\n"
      "  endgroup\n"
      "endmodule\n");
}

TEST(OptionMembers, ProceduralWriteOfANameNoLevelDeclaresIsError) {
  ExpectNoMemberErrors(InModule("  initial begin\n"
                                "    c.option.strobe = 1;\n"
                                "    cg::type_option.at_least = 2;\n"
                                "    c.cp.option.foo = 1;\n"
                                "    c.x.option.bar = 1;\n"
                                "    cg::cp::type_option.zzz = 1;\n"
                                "    cg::x::type_option.qq = 1;\n"
                                "  end\n"),
                       {{10u, "option", "strobe"},
                        {11u, "type_option", "at_least"},
                        {12u, "option", "foo"},
                        {13u, "option", "bar"},
                        {14u, "type_option", "zzz"},
                        {15u, "type_option", "qq"}});
}

TEST(OptionMembers, DISABLED_ProceduralWriteOfAMemberTheLevelLacksIsError) {
  ExpectNoMemberErrors(
      InModule("  initial begin\n"
               "    c.x.option.name = \"n\";\n"
               "    c.cp.option.name = \"n\";\n"
               "    c.cp.option.cross_num_print_missing = 2;\n"
               "    cg::x::type_option.merge_instances = 1;\n"
               "    cg::cp::type_option.distribute_first = 1;\n"
               "  end\n"),
      {{10u, "option", "name"},
       {11u, "option", "name"},
       {12u, "option", "cross_num_print_missing"},
       {13u, "type_option", "merge_instances"},
       {14u, "type_option", "distribute_first"}});
}

TEST(OptionMembers, ProceduralWriteOfEachLevelsOwnMemberIsAccepted) {
  ExpectAccepted(
      InModule("  initial begin\n"
               "    c.option.name = \"n\";\n"
               "    c.option.at_least = 2;\n"
               "    c.cp.option.weight = 2;\n"
               "    c.cp.option.at_least = 2;\n"
               "    c.x.option.cross_num_print_missing = 2;\n"
               "    cg::type_option.merge_instances = 1;\n"
               "    cg::cp::type_option.goal = 90;\n"
               "    cg::x::type_option.goal = 90;\n"
               "  end\n"));
}

TEST(OptionMembers, DISABLED_ProceduralReadOfANameNoLevelDeclaresIsError) {
  ExpectNoMemberErrors(InModule("  initial begin\n"
                                "    $display(c.option.nope);\n"
                                "    $display(cg::type_option.nope2);\n"
                                "    $display(c.x.option.foo);\n"
                                "  end\n"),
                       {{10u, "option", "nope"},
                        {11u, "type_option", "nope2"},
                        {12u, "option", "foo"}});
}

TEST(OptionMembers, ProceduralReadOfEachLevelsOwnMemberIsAccepted) {
  ExpectAccepted(InModule(
      "  initial $display(c.option.at_least, cg::type_option.weight,\n"
      "    c.cp.option.weight, c.x.option.cross_num_print_missing);\n"));
}

TEST(OptionMembers, WriteInATaskOrFunctionOfANameNoLevelDeclaresIsError) {
  ExpectNoMemberErrors(
      InModule("  task t; c.option.inTask = 1; endtask\n"
               "  function void g; cg::type_option.inFunc = 1; endfunction\n"),
      {{9u, "option", "inTask"}, {10u, "type_option", "inFunc"}});
}

TEST(OptionMembers, WriteInATaskOrFunctionOfAnOwnMemberIsAccepted) {
  ExpectAccepted(
      InModule("  task t; c.option.weight = 2; endtask\n"
               "  function void g; cg::type_option.weight = 2; endfunction\n"));
}

TEST(OptionMembers, DISABLED_PackageCovergroupNameNoLevelDeclaresIsError) {
  ExpectNoMemberErrors(
      "package p;\n"
      "  covergroup pg;\n"
      "    option.foo = 1;\n"
      "  endgroup\n"
      "endpackage\n"
      "module m;\n"
      "  p::pg c1 = new;\n"
      "  initial c1.option.zip = 1;\n"
      "endmodule\n",
      {{3u, "option", "foo"}, {8u, "option", "zip"}});
}

TEST(OptionMembers, PackageCovergroupOwnMemberIsAccepted) {
  ExpectAccepted(
      "package p;\n"
      "  covergroup pg;\n"
      "    option.weight = 2;\n"
      "  endgroup\n"
      "endpackage\n"
      "module m;\n"
      "  p::pg c1 = new;\n"
      "  initial c1.option.goal = 90;\n"
      "endmodule\n");
}

TEST(OptionMembers,
     DISABLED_CompilationUnitCovergroupNameNoLevelDeclaresIsError) {
  ExpectNoMemberErrors(
      "covergroup ug;\n"
      "  type_option.bar = 1;\n"
      "endgroup\n"
      "module m;\n"
      "  ug c2 = new;\n"
      "  initial begin\n"
      "    c2.option.zop = 1;\n"
      "    ug::type_option.at_least = 2;\n"
      "  end\n"
      "endmodule\n",
      {{2u, "type_option", "bar"},
       {7u, "option", "zop"},
       {8u, "type_option", "at_least"}});
}

TEST(OptionMembers, CompilationUnitCovergroupOwnMemberIsAccepted) {
  ExpectAccepted(
      "covergroup ug;\n"
      "  type_option.weight = 2;\n"
      "endgroup\n"
      "module m;\n"
      "  ug c2 = new;\n"
      "  initial begin\n"
      "    c2.option.at_least = 2;\n"
      "    ug::type_option.goal = 90;\n"
      "  end\n"
      "endmodule\n");
}

std::string InClass(const std::string& definition, const std::string& method) {
  return std::string(
             "module m;\n"
             "  class K;\n"
             "    bit [1:0] a;\n"
             "    covergroup kg;\n") +
         definition +
         "    endgroup\n"
         "    function new; kg = new; endfunction\n"
         "    function void set;\n" +
         method +
         "    endfunction\n"
         "  endclass\n"
         "endmodule\n";
}

TEST(OptionMembers, ClassCovergroupDefinitionNameNoLevelDeclaresIsError) {
  ExpectNoMemberErrors(InClass("      option.baz = 1;\n"
                               "      cp: coverpoint a { option.qq = 1; }\n",
                               ""),
                       {{5u, "option", "baz"}, {6u, "option", "qq"}});
}

TEST(OptionMembers, DISABLED_ClassMethodWriteOfANameTheLevelLacksIsError) {
  ExpectNoMemberErrors(
      InClass("      cp: coverpoint a;\n",
              "      kg.option.zap = 1;\n"
              "      kg.cp.option.cross_retain_auto_bins = 1;\n"),
      {{9u, "option", "zap"}, {10u, "option", "cross_retain_auto_bins"}});
}

TEST(OptionMembers, ClassCovergroupOwnMembersAreAccepted) {
  ExpectAccepted(
      InClass("      option.weight = 2;\n"
              "      cp: coverpoint a { option.at_least = 2; }\n",
              "      kg.option.goal = 90;\n"
              "      kg.cp.option.detect_overlap = 1;\n"));
}

TEST(OptionMembers, InterfaceAndProgramCovergroupNameNoLevelDeclaresIsError) {
  ExpectNoMemberErrors(
      "interface i;\n"
      "  bit [1:0] a;\n"
      "  covergroup cg;\n"
      "    option.foo = 1;\n"
      "    coverpoint a;\n"
      "  endgroup\n"
      "  cg c = new;\n"
      "  initial c.option.bar = 1;\n"
      "endinterface\n"
      "program pr;\n"
      "  bit [1:0] a;\n"
      "  covergroup cg;\n"
      "    option.foo = 1;\n"
      "    coverpoint a;\n"
      "  endgroup\n"
      "  cg c = new;\n"
      "  initial c.option.bar = 1;\n"
      "endprogram\n"
      "module m;\n"
      "  i u1();\n"
      "  pr u2();\n"
      "endmodule\n",
      {{4u, "option", "foo"},
       {8u, "option", "bar"},
       {13u, "option", "foo"},
       {17u, "option", "bar"}});
}

TEST(OptionMembers, InterfaceAndProgramCovergroupOwnMemberIsAccepted) {
  ExpectAccepted(
      "interface i;\n"
      "  bit [1:0] a;\n"
      "  covergroup cg;\n"
      "    option.weight = 2;\n"
      "    coverpoint a;\n"
      "  endgroup\n"
      "  cg c = new;\n"
      "  initial c.option.goal = 90;\n"
      "endinterface\n"
      "program pr;\n"
      "  bit [1:0] a;\n"
      "  covergroup cg;\n"
      "    option.weight = 2;\n"
      "    coverpoint a;\n"
      "  endgroup\n"
      "  cg c = new;\n"
      "  initial c.option.goal = 90;\n"
      "endprogram\n"
      "module m;\n"
      "  i u1();\n"
      "  pr u2();\n"
      "endmodule\n");
}

}  // namespace
