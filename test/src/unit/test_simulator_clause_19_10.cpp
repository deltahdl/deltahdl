#include <gtest/gtest.h>

#include "simulator/coverage.h"

using namespace delta;

namespace {

// LRM 19.10 organizes the option and type_option members of a covergroup,
// coverpoint, and cross into implicitly declared structures. Each test below
// exercises every member named in one of those structures, confirming that the
// implementation models the prescribed composition.

// LRM 19.10: covergroup `option` structure.
TEST(CoverageOrganization, CovergroupOptionMembers) {
  CoverOptions o;  // covergroup-level instance option
  o.name = "cg0";
  o.weight = 2;
  o.goal = 90.0;
  o.comment = "note";
  o.at_least = 3;
  o.auto_bin_max = 32;
  o.cross_num_print_missing = 5;
  o.cross_retain_auto_bins = false;
  o.detect_overlap = true;
  o.per_instance = true;
  o.get_inst_coverage = true;

  EXPECT_EQ(o.name, "cg0");
  EXPECT_EQ(o.weight, 2u);
  EXPECT_DOUBLE_EQ(o.goal, 90.0);
  EXPECT_EQ(o.comment, "note");
  EXPECT_EQ(o.at_least, 3u);
  EXPECT_EQ(o.auto_bin_max, 32u);
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
