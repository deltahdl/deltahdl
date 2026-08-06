#include <gtest/gtest.h>

#include <cstdint>
#include <string>
#include <type_traits>

#include "simulator/coverage.h"

using namespace delta;

namespace {

// LRM 19.10 organizes the option and type_option members of a covergroup,
// coverpoint, and cross into implicitly declared structures. Each test below
// exercises every member named in one of those structures, confirming that the
// implementation models the prescribed composition.

// LRM 19.10 prescribes the member types of each structure. The covergroup
// `option` numeric members are signed integers (int weight/goal/at_least/
// auto_bin_max), the string members are strings, and the flag members are
// single bits. Verifying the modeled types locks the composition to what the
// standard declares rather than to an incidental C++ width.
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

// LRM 19.10: coverpoint `option` composition — int weight/goal/at_least/
// auto_bin_max, string comment, bit detect_overlap.
static_assert(std::is_same_v<decltype(CoverPointOption::weight), std::int32_t>);
static_assert(std::is_same_v<decltype(CoverPointOption::goal), std::int32_t>);
static_assert(
    std::is_same_v<decltype(CoverPointOption::at_least), std::int32_t>);
static_assert(
    std::is_same_v<decltype(CoverPointOption::auto_bin_max), std::int32_t>);
static_assert(std::is_same_v<decltype(CoverPointOption::comment), std::string>);
static_assert(std::is_same_v<decltype(CoverPointOption::detect_overlap), bool>);

// LRM 19.10: cross `option` composition — int weight/goal/at_least/
// cross_num_print_missing, string comment, bit cross_retain_auto_bins.
static_assert(std::is_same_v<decltype(CrossOption::weight), std::int32_t>);
static_assert(std::is_same_v<decltype(CrossOption::goal), std::int32_t>);
static_assert(std::is_same_v<decltype(CrossOption::at_least), std::int32_t>);
static_assert(std::is_same_v<decltype(CrossOption::cross_num_print_missing),
                             std::int32_t>);
static_assert(std::is_same_v<decltype(CrossOption::comment), std::string>);
static_assert(
    std::is_same_v<decltype(CrossOption::cross_retain_auto_bins), bool>);

// LRM 19.10: covergroup `type_option` composition — int weight/goal, string
// comment, bit strobe/merge_instances/distribute_first, real real_interval.
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

// LRM 19.10: coverpoint `type_option` composition — int weight/goal, string
// comment, real real_interval.
static_assert(
    std::is_same_v<decltype(CoverPointTypeOption::weight), std::int32_t>);
static_assert(
    std::is_same_v<decltype(CoverPointTypeOption::goal), std::int32_t>);
static_assert(
    std::is_same_v<decltype(CoverPointTypeOption::comment), std::string>);
static_assert(
    std::is_same_v<decltype(CoverPointTypeOption::real_interval), double>);

// LRM 19.10: cross `type_option` composition — int weight/goal, string comment.
static_assert(std::is_same_v<decltype(CrossTypeOption::weight), std::int32_t>);
static_assert(std::is_same_v<decltype(CrossTypeOption::goal), std::int32_t>);
static_assert(std::is_same_v<decltype(CrossTypeOption::comment), std::string>);

// LRM 19.10: covergroup `option` structure.
TEST(CoverageOrganization, CovergroupOptionMembers) {
  CoverOptions o;  // covergroup-level instance option
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

// LRM 19.10: coverpoint `option` structure.
TEST(CoverageOrganization, CoverpointOptionMembers) {
  CoverPointOption o;
  EXPECT_EQ(o.weight, 1);
  EXPECT_EQ(o.goal, 100);
  EXPECT_TRUE(o.comment.empty());
  EXPECT_EQ(o.at_least, 1);
  EXPECT_EQ(o.auto_bin_max, 64);
  EXPECT_FALSE(o.detect_overlap);
}

// LRM 19.10: cross `option` structure.
TEST(CoverageOrganization, CrossOptionMembers) {
  CrossOption o;
  EXPECT_EQ(o.weight, 1);
  EXPECT_EQ(o.goal, 100);
  EXPECT_TRUE(o.comment.empty());
  EXPECT_EQ(o.at_least, 1);
  EXPECT_EQ(o.cross_num_print_missing, 0);
  EXPECT_TRUE(o.cross_retain_auto_bins);
}

// LRM 19.10: covergroup `type_option` structure.
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

// LRM 19.10: coverpoint `type_option` structure (weight, goal, comment,
// real_interval).
TEST(CoverageOrganization, CoverpointTypeOptionMembers) {
  CoverPointTypeOption t;
  EXPECT_EQ(t.weight, 1);
  EXPECT_EQ(t.goal, 100);
  EXPECT_TRUE(t.comment.empty());
  EXPECT_DOUBLE_EQ(t.real_interval, 1.0);
}

// LRM 19.10: cross `type_option` structure (weight, goal, comment only).
TEST(CoverageOrganization, CrossTypeOptionMembers) {
  CrossTypeOption t;
  EXPECT_EQ(t.weight, 1);
  EXPECT_EQ(t.goal, 100);
  EXPECT_TRUE(t.comment.empty());
}

// LRM 19.10: the option and type_option members are attached to the live
// covergroup model, so they can be read and written through it.
TEST(CoverageOrganization, MembersReachableThroughCoverGroup) {
  CoverageDB db;
  auto* g = db.CreateGroup("cg");
  g->options.per_instance = true;
  g->type_option.merge_instances = true;
  EXPECT_TRUE(g->options.per_instance);
  EXPECT_TRUE(g->type_option.merge_instances);
}

}  // namespace
