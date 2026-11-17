#include <gtest/gtest.h>

#include <cstddef>
#include <cstdint>
#include <initializer_list>
#include <iterator>
#include <span>
#include <string>
#include <type_traits>
#include <utility>

#include "fixture_simulator.h"
#include "simulator/coverage.h"
#include "simulator/coverage_types.h"

using namespace delta;

namespace {

static_assert(std::is_same_v<decltype(CoverOptions::weight), std::int32_t>);
static_assert(std::is_same_v<decltype(CoverOptions::goal), std::int32_t>);
static_assert(std::is_same_v<decltype(CoverOptions::at_least), std::int32_t>);
static_assert(
    std::is_same_v<decltype(CoverOptions::auto_bin_max), std::int32_t>);
static_assert(std::is_same_v<decltype(CoverOptions::name), std::string>);
static_assert(std::is_same_v<decltype(CoverOptions::comment), std::string>);
static_assert(std::is_same_v<decltype(CoverOptions::cross_num_print_missing),
                             std::int32_t>);
static_assert(
    std::is_same_v<decltype(CoverOptions::cross_retain_auto_bins), bool>);
static_assert(std::is_same_v<decltype(CoverOptions::detect_overlap), bool>);
static_assert(std::is_same_v<decltype(CoverOptions::per_instance), bool>);
static_assert(std::is_same_v<decltype(CoverOptions::get_inst_coverage), bool>);

static_assert(std::is_same_v<decltype(CoverPointOption::weight), std::int32_t>);
static_assert(std::is_same_v<decltype(CoverPointOption::goal), std::int32_t>);
static_assert(
    std::is_same_v<decltype(CoverPointOption::at_least), std::int32_t>);
static_assert(
    std::is_same_v<decltype(CoverPointOption::auto_bin_max), std::int32_t>);
static_assert(std::is_same_v<decltype(CoverPointOption::comment), std::string>);
static_assert(std::is_same_v<decltype(CoverPointOption::detect_overlap), bool>);

static_assert(std::is_same_v<decltype(CrossOption::weight), std::int32_t>);
static_assert(std::is_same_v<decltype(CrossOption::goal), std::int32_t>);
static_assert(std::is_same_v<decltype(CrossOption::at_least), std::int32_t>);
static_assert(std::is_same_v<decltype(CrossOption::cross_num_print_missing),
                             std::int32_t>);
static_assert(std::is_same_v<decltype(CrossOption::comment), std::string>);
static_assert(
    std::is_same_v<decltype(CrossOption::cross_retain_auto_bins), bool>);

static_assert(
    std::is_same_v<decltype(CoverGroupTypeOption::weight), std::int32_t>);
static_assert(
    std::is_same_v<decltype(CoverGroupTypeOption::goal), std::int32_t>);
static_assert(
    std::is_same_v<decltype(CoverGroupTypeOption::comment), std::string>);
static_assert(std::is_same_v<decltype(CoverGroupTypeOption::strobe), bool>);
static_assert(
    std::is_same_v<decltype(CoverGroupTypeOption::merge_instances), bool>);
static_assert(
    std::is_same_v<decltype(CoverGroupTypeOption::distribute_first), bool>);
static_assert(
    std::is_same_v<decltype(CoverGroupTypeOption::real_interval), double>);

static_assert(
    std::is_same_v<decltype(CoverPointTypeOption::weight), std::int32_t>);
static_assert(
    std::is_same_v<decltype(CoverPointTypeOption::goal), std::int32_t>);
static_assert(
    std::is_same_v<decltype(CoverPointTypeOption::comment), std::string>);
static_assert(
    std::is_same_v<decltype(CoverPointTypeOption::real_interval), double>);

static_assert(std::is_same_v<decltype(CrossTypeOption::weight), std::int32_t>);
static_assert(std::is_same_v<decltype(CrossTypeOption::goal), std::int32_t>);
static_assert(std::is_same_v<decltype(CrossTypeOption::comment), std::string>);

TEST(CoverageOrganization, CovergroupOptionMembers) {
  CoverOptions o;
  o.name = "cg0";
  o.weight = 2;
  o.goal = 90;
  o.comment = "note";
  o.at_least = 3;
  o.auto_bin_max = 32;
  o.cross_num_print_missing = 5;
  o.cross_retain_auto_bins = false;
  o.detect_overlap = true;
  o.per_instance = true;
  o.get_inst_coverage = true;

  EXPECT_EQ(o.name, "cg0");
  EXPECT_EQ(o.weight, 2);
  EXPECT_EQ(o.goal, 90);
  EXPECT_EQ(o.comment, "note");
  EXPECT_EQ(o.at_least, 3);
  EXPECT_EQ(o.auto_bin_max, 32);
  EXPECT_EQ(o.cross_num_print_missing, 5);
  EXPECT_FALSE(o.cross_retain_auto_bins);
  EXPECT_TRUE(o.detect_overlap);
  EXPECT_TRUE(o.per_instance);
  EXPECT_TRUE(o.get_inst_coverage);
}

TEST(CoverageOrganization, CoverpointOptionMembers) {
  CoverPointOption o;
  EXPECT_EQ(o.weight, 1);
  EXPECT_EQ(o.goal, 100);
  EXPECT_TRUE(o.comment.empty());
  EXPECT_EQ(o.at_least, 1);
  EXPECT_EQ(o.auto_bin_max, 64);
  EXPECT_FALSE(o.detect_overlap);
}

TEST(CoverageOrganization, CrossOptionMembers) {
  CrossOption o;
  EXPECT_EQ(o.weight, 1);
  EXPECT_EQ(o.goal, 100);
  EXPECT_TRUE(o.comment.empty());
  EXPECT_EQ(o.at_least, 1);
  EXPECT_EQ(o.cross_num_print_missing, 0);
  EXPECT_TRUE(o.cross_retain_auto_bins);
}

TEST(CoverageOrganization, CovergroupTypeOptionMembers) {
  CoverGroupTypeOption t;
  t.weight = 1;
  t.goal = 100;
  t.comment = "";
  t.strobe = true;
  t.merge_instances = true;
  t.distribute_first = true;
  t.real_interval = 0.5;

  EXPECT_TRUE(t.strobe);
  EXPECT_TRUE(t.merge_instances);
  EXPECT_TRUE(t.distribute_first);
  EXPECT_DOUBLE_EQ(t.real_interval, 0.5);
}

TEST(CoverageOrganization, CoverpointTypeOptionMembers) {
  CoverPointTypeOption t;
  EXPECT_EQ(t.weight, 1);
  EXPECT_EQ(t.goal, 100);
  EXPECT_TRUE(t.comment.empty());
  EXPECT_DOUBLE_EQ(t.real_interval, 1.0);
}

TEST(CoverageOrganization, CrossTypeOptionMembers) {
  CrossTypeOption t;
  EXPECT_EQ(t.weight, 1);
  EXPECT_EQ(t.goal, 100);
  EXPECT_TRUE(t.comment.empty());
}

TEST(CoverageOrganization, MembersReachableThroughCoverGroup) {
  CoverageDB db;
  auto* g = db.CreateGroup("cg");
  g->options.per_instance = true;
  g->type_option.merge_instances = true;
  EXPECT_TRUE(g->options.per_instance);
  EXPECT_TRUE(g->type_option.merge_instances);
}

const char kOptionLevels[] =
    "module t;\n"
    "  bit [1:0] a, b;\n"
    "  covergroup cg;\n"
    "    cp: coverpoint a;\n"
    "    cq: coverpoint b;\n"
    "    x: cross cp, cq;\n"
    "  endgroup\n"
    "  cg c = new;\n"
    "  initial begin\n";

const char* const kIntMembers[] = {"c.option.weight",
                                   "c.option.goal",
                                   "c.option.at_least",
                                   "c.option.auto_bin_max",
                                   "c.option.cross_num_print_missing",
                                   "c.cp.option.weight",
                                   "c.cp.option.goal",
                                   "c.cp.option.at_least",
                                   "c.cp.option.auto_bin_max",
                                   "c.x.option.weight",
                                   "c.x.option.goal",
                                   "c.x.option.at_least",
                                   "c.x.option.cross_num_print_missing",
                                   "cg::type_option.weight",
                                   "cg::type_option.goal",
                                   "cg::cp::type_option.weight",
                                   "cg::cp::type_option.goal",
                                   "cg::x::type_option.weight",
                                   "cg::x::type_option.goal"};

const char* const kBitMembers[] = {
    "c.option.cross_retain_auto_bins", "c.option.detect_overlap",
    "c.option.per_instance",           "c.option.get_inst_coverage",
    "c.cp.option.detect_overlap",      "c.x.option.cross_retain_auto_bins",
    "cg::type_option.strobe",          "cg::type_option.merge_instances",
    "cg::type_option.distribute_first"};

const char* const kStringMembers[] = {"c.option.name",
                                      "c.option.comment",
                                      "c.cp.option.comment",
                                      "c.x.option.comment",
                                      "cg::type_option.comment",
                                      "cg::cp::type_option.comment",
                                      "cg::x::type_option.comment"};

const char* const kRealMembers[] = {"cg::type_option.real_interval",
                                    "cg::cp::type_option.real_interval"};

std::string RunLevels(const std::string& statements) {
  SimFixture f;
  return RunCapture(std::string(kOptionLevels) + statements +
                        "  end\n"
                        "endmodule\n",
                    f);
}

std::string EachMember(std::span<const char* const> members, const char* format,
                       const char* call) {
  std::string statements;
  for (const char* member : members) {
    statements.append("    $display(\"")
        .append(format)
        .append("\", ")
        .append(call)
        .append("(")
        .append(member)
        .append("));\n");
  }
  return statements;
}

std::string Repeated(const std::string& line, std::size_t count) {
  std::string lines;
  for (std::size_t i = 0; i < count; ++i) lines.append(line).append("\n");
  return lines;
}

TEST(OptionMemberTypes, DISABLED_EachMemberHasTheTypeItsStructureDeclares) {
  for (const auto& [members, type] : std::initializer_list<
           std::pair<std::span<const char* const>, std::string>>{
           {kIntMembers, "int"},
           {kBitMembers, "bit"},
           {kStringMembers, "string"},
           {kRealMembers, "real"}}) {
    EXPECT_EQ(RunLevels(EachMember(members, "%s", "$typename")),
              Repeated(type, members.size()))
        << type;
  }
}

TEST(OptionMemberTypes, IntMembersAreThirtyTwoBitsAndBitMembersOne) {
  EXPECT_EQ(RunLevels(EachMember(kIntMembers, "%0d", "$bits")),
            Repeated("32", std::size(kIntMembers)));
  EXPECT_EQ(RunLevels(EachMember(kBitMembers, "%0d", "$bits")),
            Repeated("1", std::size(kBitMembers)));
}

TEST(OptionMemberTypes, IntMembersAreSignedAndTruncateWiderValues) {
  EXPECT_EQ(RunLevels("    c.option.goal = -3;\n"
                      "    c.cp.option.at_least = -1;\n"
                      "    c.x.option.weight = 33'h1_0000_0005;\n"
                      "    cg::type_option.goal = -7;\n"
                      "    $display(\"%0d %0d %0d %0d %0d\", c.option.goal,\n"
                      "      c.option.goal < 0, c.cp.option.at_least,\n"
                      "      c.x.option.weight, cg::type_option.goal);\n"),
            "-3 1 -1 5 -7\n");
}

std::string RunDefined(const std::string& statements) {
  SimFixture f;
  return RunCapture(
      std::string("module t;\n"
                  "  bit [1:0] a, b;\n"
                  "  covergroup cg;\n"
                  "    option.detect_overlap = 2;\n"
                  "    type_option.real_interval = 0.25;\n"
                  "    cp: coverpoint a { option.detect_overlap = 3;\n"
                  "      type_option.real_interval = 0.5; }\n"
                  "    cq: coverpoint b;\n"
                  "    x: cross cp, cq { option.cross_retain_auto_bins = 2; }\n"
                  "  endgroup\n"
                  "  cg c = new;\n"
                  "  initial begin\n") +
          statements +
          "  end\n"
          "endmodule\n",
      f);
}

TEST(OptionMemberTypes, DISABLED_BitMembersKeepOnlyTheLowBit) {
  EXPECT_EQ(RunDefined("    cg::type_option.merge_instances = 2;\n"
                       "    cg::type_option.distribute_first = 3;\n"
                       "    $display(\"%0d %0d %0d %0d %0d\",\n"
                       "      c.option.detect_overlap,\n"
                       "      c.cp.option.detect_overlap,\n"
                       "      c.x.option.cross_retain_auto_bins,\n"
                       "      cg::type_option.merge_instances,\n"
                       "      cg::type_option.distribute_first);\n"),
            "0 1 0 0 1\n");
}

TEST(OptionMemberTypes, RealIntervalHoldsAFraction) {
  EXPECT_EQ(RunDefined("    $display(\"%0.2f %0.2f\",\n"
                       "      cg::type_option.real_interval,\n"
                       "      cg::cp::type_option.real_interval);\n"),
            "0.25 0.50\n");
}

TEST(OptionMemberTypes, StringMembersHoldAString) {
  EXPECT_EQ(RunLevels("    c.option.comment = \"g\";\n"
                      "    c.cp.option.comment = \"p\";\n"
                      "    c.x.option.comment = \"x\";\n"
                      "    cg::cp::type_option.comment = \"tp\";\n"
                      "    cg::x::type_option.comment = \"tx\";\n"
                      "    $display(\"%s %s %s %s %s\", c.option.comment,\n"
                      "      c.cp.option.comment, c.x.option.comment,\n"
                      "      cg::cp::type_option.comment,\n"
                      "      cg::x::type_option.comment);\n"),
            "g p x tp tx\n");
}

}  // namespace
