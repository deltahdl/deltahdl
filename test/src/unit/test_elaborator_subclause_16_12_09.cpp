#include <gtest/gtest.h>

#include "helpers_named_property_places.h"

namespace {

TEST(FollowedByAntecedent,
     DISABLED_ANamedPropertyAsTheAntecedentIsReportedInEachPlace) {
  ExpectNamedSpecsReported(
      {"p #-# c", "p #=# c", "pa(a, b) #-# c", "pb #=# c", "(pb) #-# c"},
      {"pk::p #-# c", "pk::pb #=# c"});
}

TEST(FollowedByAntecedent, ANamedSequenceAsTheAntecedentIsAcceptedInEachPlace) {
  ExpectNamedSpecsAccepted(
      {"s #-# c", "s #=# c", "sa(a, b) #-# c", "(s) #=# c", "a #-# p",
       "s #=# pa(a, b)", "sa(a, b) ##1 s #-# pb"},
      {"pk::s #-# c", "a #=# pk::p"});
}

}  // namespace
