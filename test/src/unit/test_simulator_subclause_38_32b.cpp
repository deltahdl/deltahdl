#include <gtest/gtest.h>

#include <cstddef>
#include <vector>

#include "helpers_vpi_delays_fixture.h"
#include "simulator/vpi_constants.h"
#include "simulator/vpi_object.h"
#include "simulator/vpi_user.h"

namespace delta {
namespace {

class PutDelaysOfAnObject : public VpiDelaysSimBase {
 protected:
  static VpiDelayInfo Seeded(double delay) {
    VpiDelayInfo info;
    info.delay = delay;
    return info;
  }

  PLI_INT32 PutCounting(VpiHandle obj, int count, int mtm, int pulsere) {
    const int kPerDelay = (mtm != 0 ? 3 : 1) * (pulsere != 0 ? 3 : 1);
    std::vector<s_vpi_time> da(static_cast<size_t>(count * kPerDelay) + 1);
    for (size_t i = 0; i < da.size(); ++i) {
      da[i].real = static_cast<double>(i + 1);
    }
    s_vpi_delay delay = {};
    delay.da = da.data();
    delay.no_of_delays = count;
    delay.time_type = vpiScaledRealTime;
    delay.mtm_flag = mtm;
    delay.pulsere_flag = pulsere;
    vpi_ctx_.ResetErrorStatus();
    vpi_put_delays(VpiHandleOf(obj), &delay);
    return vpi_ctx_.LastError().level;
  }

  void ExpectRefusedAndKept(int type, int count) {
    VpiHandle obj = MakeDelayObject(type, {Seeded(500.0)});
    EXPECT_EQ(PutCounting(obj, count, 0, 0), kVpiError) << "count " << count;
    ASSERT_EQ(obj->delays.size(), 1u) << "count " << count;
    EXPECT_DOUBLE_EQ(obj->delays[0].delay, 500.0) << "count " << count;
  }

  void ExpectAccepted(int type, int count) {
    VpiHandle obj =
        MakeDelayObject(type, std::vector<VpiDelayInfo>(count, Seeded(500.0)));
    EXPECT_EQ(PutCounting(obj, count, 0, 0), 0) << "count " << count;
    ASSERT_EQ(obj->delays.size(), static_cast<size_t>(count));
    EXPECT_DOUBLE_EQ(obj->delays[count - 1].delay, count) << "count " << count;
  }
};

TEST_F(PutDelaysOfAnObject, PulsereOnlyTheSecondDelayBeginsAtTheFourthEntry) {
  VpiHandle path =
      MakeDelayObject(vpiModPath, {VpiDelayInfo{}, VpiDelayInfo{}});
  ASSERT_EQ(PutCounting(path, 2, 0, 1), 0);
  ASSERT_EQ(path->delays.size(), 2u);
  EXPECT_DOUBLE_EQ(path->delays[1].delay, 4.0);
  EXPECT_DOUBLE_EQ(path->delays[1].reject, 5.0);
  EXPECT_DOUBLE_EQ(path->delays[1].error, 6.0);
}

TEST_F(PutDelaysOfAnObject, BothFlagsTheSecondDelayBeginsAtTheTenthEntry) {
  VpiHandle path =
      MakeDelayObject(vpiModPath, {VpiDelayInfo{}, VpiDelayInfo{}});
  ASSERT_EQ(PutCounting(path, 2, 1, 1), 0);
  ASSERT_EQ(path->delays.size(), 2u);
  EXPECT_DOUBLE_EQ(path->delays[1].min_delay, 10.0);
  EXPECT_DOUBLE_EQ(path->delays[1].max_delay, 12.0);
  EXPECT_DOUBLE_EQ(path->delays[1].typ_reject, 14.0);
  EXPECT_DOUBLE_EQ(path->delays[1].max_error, 18.0);
}

TEST_F(PutDelaysOfAnObject, APrimitiveRefusesNoneOrOneDelay) {
  ExpectRefusedAndKept(vpiPrimitive, 0);
  ExpectRefusedAndKept(vpiPrimitive, 1);
}

TEST_F(PutDelaysOfAnObject, AModulePathAcceptsThreeSixOrTwelveDelays) {
  ExpectAccepted(vpiModPath, 3);
  ExpectAccepted(vpiModPath, 6);
  ExpectAccepted(vpiModPath, 12);
}

TEST_F(PutDelaysOfAnObject, AModulePathRefusesEveryOtherCount) {
  for (const int kCount : {0, 4, 5, 7, 8, 9, 10, 11, 13}) {
    ExpectRefusedAndKept(vpiModPath, kCount);
  }
}

TEST_F(PutDelaysOfAnObject, AnIntermodulePathAcceptsThreeDelays) {
  ExpectAccepted(vpiInterModPath, 3);
}

TEST_F(PutDelaysOfAnObject, AnIntermodulePathRefusesOneOrFourDelays) {
  ExpectRefusedAndKept(vpiInterModPath, 1);
  ExpectRefusedAndKept(vpiInterModPath, 4);
}

TEST_F(PutDelaysOfAnObject, ASimTimeEntryTakesItsHighWord) {
  VpiHandle prim =
      MakeDelayObject(vpiPrimitive, {VpiDelayInfo{}, VpiDelayInfo{}});
  s_vpi_time da[2] = {};
  da[0].high = 1;
  da[0].low = 5;
  da[1].low = 7;
  s_vpi_delay delay = {};
  delay.da = da;
  delay.no_of_delays = 2;
  delay.time_type = vpiSimTime;
  vpi_put_delays(VpiHandleOf(prim), &delay);
  ASSERT_EQ(prim->delays.size(), 2u);
  EXPECT_DOUBLE_EQ(prim->delays[0].delay, 4294967301.0);
  EXPECT_DOUBLE_EQ(prim->delays[1].delay, 7.0);
}

TEST_F(PutDelaysOfAnObject, AMinTypMaxDelayOnlyPutKeepsEveryLimit) {
  VpiDelayInfo seeded;
  seeded.min_reject = 101.0;
  seeded.typ_reject = 102.0;
  seeded.max_reject = 103.0;
  seeded.min_error = 104.0;
  seeded.typ_error = 105.0;
  seeded.max_error = 106.0;
  VpiHandle path = MakeDelayObject(vpiModPath, {seeded});
  ASSERT_EQ(PutCounting(path, 1, 1, 0), 0);
  ASSERT_EQ(path->delays.size(), 1u);
  const VpiDelayInfo& after = path->delays[0];
  EXPECT_DOUBLE_EQ(after.min_delay, 1.0);
  EXPECT_DOUBLE_EQ(after.max_delay, 3.0);
  EXPECT_DOUBLE_EQ(after.min_reject, 101.0);
  EXPECT_DOUBLE_EQ(after.typ_reject, 102.0);
  EXPECT_DOUBLE_EQ(after.max_reject, 103.0);
  EXPECT_DOUBLE_EQ(after.min_error, 104.0);
  EXPECT_DOUBLE_EQ(after.typ_error, 105.0);
  EXPECT_DOUBLE_EQ(after.max_error, 106.0);
}

TEST_F(PutDelaysOfAnObject, AnIntermodulePathKeepsLimitsAnEarlierPutSet) {
  VpiHandle path =
      MakeDelayObject(vpiInterModPath, {VpiDelayInfo{}, VpiDelayInfo{}});
  ASSERT_EQ(PutCounting(path, 2, 0, 1), 0);
  s_vpi_time da[2] = {};
  da[0].real = 40.0;
  da[1].real = 50.0;
  s_vpi_delay delay = {};
  delay.da = da;
  delay.no_of_delays = 2;
  delay.time_type = vpiScaledRealTime;
  vpi_put_delays(VpiHandleOf(path), &delay);

  s_vpi_time out[6] = {};
  s_vpi_delay get = {};
  get.da = out;
  get.no_of_delays = 2;
  get.time_type = vpiScaledRealTime;
  get.pulsere_flag = 1;
  vpi_get_delays(VpiHandleOf(path), &get);
  EXPECT_DOUBLE_EQ(out[0].real, 40.0);
  EXPECT_DOUBLE_EQ(out[1].real, 2.0);
  EXPECT_DOUBLE_EQ(out[2].real, 3.0);
  EXPECT_DOUBLE_EQ(out[3].real, 50.0);
  EXPECT_DOUBLE_EQ(out[4].real, 5.0);
  EXPECT_DOUBLE_EQ(out[5].real, 6.0);
}

}  // namespace
}  // namespace delta
