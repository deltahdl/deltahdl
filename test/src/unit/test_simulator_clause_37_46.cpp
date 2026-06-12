#include <gtest/gtest.h>

#include <algorithm>
#include <vector>

#include "simulator/sv_vpi_user.h"
#include "simulator/vpi.h"

namespace delta {
namespace {

// §37.46 Net drivers and loads: the vpiDriver and vpiLoad edges relate a net to
// the objects that drive it and the objects that load (read) it. The figure's
// driver kinds are a port, a force, a delay terminal, a continuous assignment
// (whole or single bit), and a primitive terminal; the load kinds are those
// without a port but with an assignment statement, since a net is loaded - not
// driven - by an assignment statement, and a port loads a net only through the
// complex-expression rule below. Detail 1 refines the load side: a complex,
// non-concatenation expression on an input port loads the nets it reads, the
// port carrying it is the load object reported, and that expression is reached
// through vpi_handle(vpiHighConn, port). These are exercised through the public
// iterate/scan and handle API.

// Walk an iterator to completion, collecting every object it yields in order.
std::vector<VpiHandle> Collect(VpiContext& ctx, VpiHandle iterator) {
  std::vector<VpiHandle> objects;
  if (!iterator) return objects;
  while (VpiHandle next = ctx.Scan(iterator)) objects.push_back(next);
  return objects;
}

bool Contains(const std::vector<VpiHandle>& objects, VpiHandle wanted) {
  return std::find(objects.begin(), objects.end(), wanted) != objects.end();
}

// Figure (net drivers): vpiDriver on a net reaches every net-driver kind - a
// port, a force, a delay terminal, a continuous assignment, a single bit of one,
// and a primitive terminal - while skipping children that are not drivers. The
// net case differs from a variable (§37.21): an assignment statement loads a net
// but does not drive it, so it is excluded from the driver iteration here.
TEST(NetDriversAndLoads, DriverIterationReachesEveryNetDriverKind) {
  VpiContext ctx;

  VpiObject port;
  port.type = vpiPort;
  VpiObject force;
  force.type = vpiForce;
  VpiObject delay_term;
  delay_term.type = vpiDelayTerm;
  VpiObject cont_assign;
  cont_assign.type = vpiContAssign;
  VpiObject cont_assign_bit;
  cont_assign_bit.type = vpiContAssignBit;
  VpiObject prim_term;
  prim_term.type = vpiPrimTerm;

  // Not a net driver: an assignment statement loads but never drives a net, and
  // an unrelated child is no driver at all.
  VpiObject assign_stmt;
  assign_stmt.type = vpiAssignStmt;
  VpiObject unrelated;
  unrelated.type = vpiTypespec;

  VpiObject net;
  net.type = vpiNet;
  net.children = {&port,       &force,           &delay_term, &cont_assign,
                  &cont_assign_bit, &prim_term,  &assign_stmt, &unrelated};

  std::vector<VpiHandle> drivers = Collect(ctx, ctx.Iterate(vpiDriver, &net));
  ASSERT_EQ(drivers.size(), 6u);
  EXPECT_TRUE(Contains(drivers, &port));
  EXPECT_TRUE(Contains(drivers, &force));
  EXPECT_TRUE(Contains(drivers, &delay_term));
  EXPECT_TRUE(Contains(drivers, &cont_assign));
  EXPECT_TRUE(Contains(drivers, &cont_assign_bit));
  EXPECT_TRUE(Contains(drivers, &prim_term));
  EXPECT_FALSE(Contains(drivers, &assign_stmt));
  EXPECT_FALSE(Contains(drivers, &unrelated));
}

// Figure (net loads): vpiLoad on a net reaches the net-load kinds - a delay
// terminal, an assignment statement, a force, a continuous assignment, a single
// bit of one, and a primitive terminal. A plain port that merely drives the net
// (no complex expression) is not a load, so it is left out even though it is a
// child of the net.
TEST(NetDriversAndLoads, LoadIterationReachesNetLoadKindsExcludingPlainPort) {
  VpiContext ctx;

  VpiObject delay_term;
  delay_term.type = vpiDelayTerm;
  VpiObject assign_stmt;
  assign_stmt.type = vpiAssignStmt;
  VpiObject force;
  force.type = vpiForce;
  VpiObject cont_assign;
  cont_assign.type = vpiContAssign;
  VpiObject cont_assign_bit;
  cont_assign_bit.type = vpiContAssignBit;
  VpiObject prim_term;
  prim_term.type = vpiPrimTerm;

  // A driver-only port: it carries no complex expression on an input, so detail
  // 1 does not make it a load.
  VpiObject driver_port;
  driver_port.type = vpiPort;

  VpiObject net;
  net.type = vpiNet;
  net.children = {&delay_term,      &assign_stmt, &force,       &cont_assign,
                  &cont_assign_bit, &prim_term,   &driver_port};

  std::vector<VpiHandle> loads = Collect(ctx, ctx.Iterate(vpiLoad, &net));
  ASSERT_EQ(loads.size(), 6u);
  EXPECT_TRUE(Contains(loads, &delay_term));
  EXPECT_TRUE(Contains(loads, &assign_stmt));
  EXPECT_TRUE(Contains(loads, &force));
  EXPECT_TRUE(Contains(loads, &cont_assign));
  EXPECT_TRUE(Contains(loads, &cont_assign_bit));
  EXPECT_TRUE(Contains(loads, &prim_term));
  EXPECT_FALSE(Contains(loads, &driver_port));
}

// Detail 1 (both shalls): a complex expression that is not a concatenation on an
// input port shall be considered a load for each net it reads, and that complex
// expression shall be reachable through vpi_handle(vpiHighConn, port). Modeled
// on the clause's example - trinet feeding ram's fourth port through !trinet -
// the input port appears when iterating the net's loads, and its vpiHighConn
// reaches the operation.
TEST(NetDriversAndLoads, ComplexExpressionInputPortIsLoadAndHighConnReachesExpr) {
  VpiContext ctx;

  // The complex connection on the port: an operation (here a logical negation),
  // not a simple reference and not a concatenation.
  VpiObject complex_expr;
  complex_expr.type = vpiOperation;
  complex_expr.op_type = vpiNotOp;

  VpiObject port;
  port.type = vpiPort;
  port.direction = vpiInput;
  port.high_conn = &complex_expr;

  VpiObject net;
  net.type = vpiNet;
  net.children = {&port};

  std::vector<VpiHandle> loads = Collect(ctx, ctx.Iterate(vpiLoad, &net));
  ASSERT_EQ(loads.size(), 1u);
  EXPECT_TRUE(Contains(loads, &port));

  // Shall #2: the complex expression is reached through the port's vpiHighConn.
  EXPECT_EQ(VpiHandleC(vpiHighConn, &port), &complex_expr);
}

// Detail 1 (concatenation carve-out): a concatenation on an input port does not
// make the whole port a load - the concatenation's operands connect their nets
// individually - so the port is excluded from the net's load iteration.
TEST(NetDriversAndLoads, ConcatenationOnInputPortIsNotLoad) {
  VpiContext ctx;

  VpiObject concat;
  concat.type = vpiOperation;
  concat.op_type = vpiConcatOp;

  VpiObject port;
  port.type = vpiPort;
  port.direction = vpiInput;
  port.high_conn = &concat;

  VpiObject net;
  net.type = vpiNet;
  net.children = {&port};

  std::vector<VpiHandle> loads = Collect(ctx, ctx.Iterate(vpiLoad, &net));
  EXPECT_FALSE(Contains(loads, &port));
}

// Detail 1 (complex requirement): a simple reference on an input port is a
// direct connection, not a complex expression, so it does not make the port a
// load under detail 1's rule.
TEST(NetDriversAndLoads, SimpleReferenceOnInputPortIsNotComplexLoad) {
  VpiContext ctx;

  VpiObject ref;
  ref.type = vpiRefObj;

  VpiObject port;
  port.type = vpiPort;
  port.direction = vpiInput;
  port.high_conn = &ref;

  VpiObject net;
  net.type = vpiNet;
  net.children = {&port};

  std::vector<VpiHandle> loads = Collect(ctx, ctx.Iterate(vpiLoad, &net));
  EXPECT_FALSE(Contains(loads, &port));
}

// Detail 1 (input requirement): the rule is scoped to input ports. A complex,
// non-concatenation expression on an output port does not make the port a load,
// so it is excluded from the net's load iteration.
TEST(NetDriversAndLoads, ComplexExpressionOnOutputPortIsNotLoad) {
  VpiContext ctx;

  VpiObject complex_expr;
  complex_expr.type = vpiOperation;
  complex_expr.op_type = vpiNotOp;

  VpiObject port;
  port.type = vpiPort;
  port.direction = vpiOutput;
  port.high_conn = &complex_expr;

  VpiObject net;
  net.type = vpiNet;
  net.children = {&port};

  std::vector<VpiHandle> loads = Collect(ctx, ctx.Iterate(vpiLoad, &net));
  EXPECT_FALSE(Contains(loads, &port));
}

// Detail 1 (edge - no expression present): the rule applies to a complex
// expression carried on an input port, so an input port with no connection
// expression at all has nothing complex to read the net and is not a load. The
// load iteration still works for the net's other loads, confirming the port is
// specifically excluded rather than the iteration simply yielding nothing.
TEST(NetDriversAndLoads, InputPortWithoutHighConnectionIsNotLoad) {
  VpiContext ctx;

  // An input port with no high connection - no expression to make it a load.
  VpiObject port;
  port.type = vpiPort;
  port.direction = vpiInput;

  VpiObject force;
  force.type = vpiForce;

  VpiObject net;
  net.type = vpiNet;
  net.children = {&port, &force};

  std::vector<VpiHandle> loads = Collect(ctx, ctx.Iterate(vpiLoad, &net));
  EXPECT_TRUE(Contains(loads, &force));
  EXPECT_FALSE(Contains(loads, &port));
}

}  // namespace
}  // namespace delta
