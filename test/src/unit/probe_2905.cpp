#include <gtest/gtest.h>

#include "fixture_parser.h"
#include "parser/ast.h"
#include "simulator/udp_eval.h"

using namespace delta;

TEST(Probe2905, Latch) {
  auto r = Parse(
      "primitive latch (q, ena_, data);\n"
      "  output q; reg q;\n"
      "  input ena_, data;\n"
      "  table\n"
      "  // ena_ data : q : q+\n"
      "    0 1 : ? : 1 ;\n"
      "    0 0 : ? : 0 ;\n"
      "    1 ? : ? : - ;\n"
      "  endtable\n"
      "endprimitive\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->udps.size(), 1u);
  const UdpDecl& d = *r.cu->udps[0];
  EXPECT_TRUE(d.is_sequential);
  EXPECT_EQ(d.table.size(), 3u);
  EXPECT_EQ(d.table[0].current_state, '?');
  EXPECT_EQ(d.table[2].output, '-');
  fprintf(stderr, "seq=%d rows=%zu init=%c cs0=%c out2=%c\n", d.is_sequential,
          d.table.size(), d.initial_value, d.table[0].current_state,
          d.table[2].output);
}
