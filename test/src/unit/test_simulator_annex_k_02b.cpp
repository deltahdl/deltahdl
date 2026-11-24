#include <gtest/gtest.h>

#include <cstdarg>
#include <cstddef>
#include <cstdint>
#include <type_traits>

#include "simulator/vpi_user.h"

namespace {

template <typename Expected, typename Actual>
bool Same() {
  return std::is_same_v<Expected, Actual>;
}

TEST(VpiRoutinePrototypes,
     TheCallbackAndHandleRoutinesHaveTheListingsPrototypes) {
  EXPECT_TRUE((Same<vpiHandle(p_cb_data), decltype(vpi_register_cb)>()));
  EXPECT_TRUE((Same<PLI_INT32(vpiHandle), decltype(vpi_remove_cb)>()));
  EXPECT_TRUE((Same<void(vpiHandle, p_cb_data), decltype(vpi_get_cb_info)>()));
  EXPECT_TRUE(
      (Same<vpiHandle(p_vpi_systf_data), decltype(vpi_register_systf)>()));
  EXPECT_TRUE((
      Same<void(vpiHandle, p_vpi_systf_data), decltype(vpi_get_systf_info)>()));
  EXPECT_TRUE(
      (Same<vpiHandle(PLI_BYTE8*, vpiHandle), decltype(vpi_handle_by_name)>()));
  EXPECT_TRUE(
      (Same<vpiHandle(vpiHandle, PLI_INT32), decltype(vpi_handle_by_index)>()));
}

TEST(VpiRoutinePrototypes,
     TheTraversalAndPropertyRoutinesHaveTheListingsPrototypes) {
  EXPECT_TRUE((Same<vpiHandle(PLI_INT32, vpiHandle), decltype(vpi_handle)>()));
  EXPECT_TRUE((Same<vpiHandle(PLI_INT32, vpiHandle, vpiHandle, ...),
                    decltype(vpi_handle_multi)>()));
  EXPECT_TRUE((Same<vpiHandle(PLI_INT32, vpiHandle), decltype(vpi_iterate)>()));
  EXPECT_TRUE((Same<vpiHandle(vpiHandle), decltype(vpi_scan)>()));
  EXPECT_TRUE((Same<PLI_INT32(PLI_INT32, vpiHandle), decltype(vpi_get)>()));
  EXPECT_TRUE((Same<PLI_INT64(PLI_INT32, vpiHandle), decltype(vpi_get64)>()));
  EXPECT_TRUE(
      (Same<PLI_BYTE8*(PLI_INT32, vpiHandle), decltype(vpi_get_str)>()));
}

TEST(VpiRoutinePrototypes,
     TheDelayValueAndTimeRoutinesHaveTheListingsPrototypes) {
  EXPECT_TRUE((Same<void(vpiHandle, p_vpi_delay), decltype(vpi_get_delays)>()));
  EXPECT_TRUE((Same<void(vpiHandle, p_vpi_delay), decltype(vpi_put_delays)>()));
  EXPECT_TRUE((Same<void(vpiHandle, p_vpi_value), decltype(vpi_get_value)>()));
  EXPECT_TRUE((Same<vpiHandle(vpiHandle, p_vpi_value, p_vpi_time, PLI_INT32),
                    decltype(vpi_put_value)>()));
  EXPECT_TRUE((Same<void(vpiHandle, p_vpi_arrayvalue, PLI_INT32*, PLI_UINT32),
                    decltype(vpi_get_value_array)>()));
  EXPECT_TRUE((Same<void(vpiHandle, p_vpi_arrayvalue, PLI_INT32*, PLI_UINT32),
                    decltype(vpi_put_value_array)>()));
  EXPECT_TRUE((Same<void(vpiHandle, p_vpi_time), decltype(vpi_get_time)>()));
}

TEST(VpiRoutinePrototypes, TheInputOutputRoutinesHaveTheListingsPrototypes) {
  EXPECT_TRUE((Same<PLI_UINT32(PLI_BYTE8*), decltype(vpi_mcd_open)>()));
  EXPECT_TRUE((Same<PLI_UINT32(PLI_UINT32), decltype(vpi_mcd_close)>()));
  EXPECT_TRUE((Same<PLI_BYTE8*(PLI_UINT32), decltype(vpi_mcd_name)>()));
  EXPECT_TRUE((Same<PLI_INT32(PLI_UINT32, PLI_BYTE8*, ...),
                    decltype(vpi_mcd_printf)>()));
  EXPECT_TRUE((Same<PLI_INT32(PLI_BYTE8*, ...), decltype(vpi_printf)>()));
  EXPECT_TRUE((Same<PLI_INT32(PLI_BYTE8*, va_list), decltype(vpi_vprintf)>()));
  EXPECT_TRUE((Same<PLI_INT32(PLI_UINT32, PLI_BYTE8*, va_list),
                    decltype(vpi_mcd_vprintf)>()));
  EXPECT_TRUE((Same<PLI_INT32(), decltype(vpi_flush)>()));
  EXPECT_TRUE((Same<PLI_INT32(PLI_UINT32), decltype(vpi_mcd_flush)>()));
}

TEST(VpiRoutinePrototypes, TheUtilityRoutinesHaveTheListingsPrototypes) {
  EXPECT_TRUE(
      (Same<PLI_INT32(vpiHandle, vpiHandle), decltype(vpi_compare_objects)>()));
  EXPECT_TRUE((Same<PLI_INT32(p_vpi_error_info), decltype(vpi_chk_error)>()));
  EXPECT_TRUE((Same<PLI_INT32(vpiHandle), decltype(vpi_free_object)>()));
  EXPECT_TRUE((Same<PLI_INT32(vpiHandle), decltype(vpi_release_handle)>()));
  EXPECT_TRUE(
      (Same<PLI_INT32(p_vpi_vlog_info), decltype(vpi_get_vlog_info)>()));
  EXPECT_TRUE((Same<PLI_INT32(PLI_INT32, PLI_BYTE8*, PLI_INT32),
                    decltype(vpi_get_data)>()));
  EXPECT_TRUE((Same<PLI_INT32(PLI_INT32, PLI_BYTE8*, PLI_INT32),
                    decltype(vpi_put_data)>()));
  EXPECT_TRUE((Same<void*(vpiHandle), decltype(vpi_get_userdata)>()));
  EXPECT_TRUE(
      (Same<PLI_INT32(vpiHandle, void*), decltype(vpi_put_userdata)>()));
  EXPECT_TRUE((Same<PLI_INT32(PLI_INT32, ...), decltype(vpi_control)>()));
  EXPECT_TRUE((Same<vpiHandle(vpiHandle, PLI_INT32, PLI_INT32*),
                    decltype(vpi_handle_by_multi_index)>()));
}

TEST(VpiSizedTypes, TheSizedTypesNameTheListingsCTypes) {
  EXPECT_TRUE((Same<int64_t, PLI_INT64>()));
  EXPECT_TRUE((Same<uint64_t, PLI_UINT64>()));
  EXPECT_TRUE((Same<int, PLI_INT32>()));
  EXPECT_TRUE((Same<unsigned int, PLI_UINT32>()));
  EXPECT_TRUE((Same<short, PLI_INT16>()));
  EXPECT_TRUE((Same<unsigned short, PLI_UINT16>()));
  EXPECT_TRUE((Same<char, PLI_BYTE8>()));
  EXPECT_TRUE((Same<unsigned char, PLI_UBYTE8>()));
  EXPECT_TRUE((Same<PLI_UINT32*, vpiHandle>()));
}

TEST(VpiStructures, TheTimeStructureIsTheListings) {
  EXPECT_TRUE((Same<struct t_vpi_time, s_vpi_time>()));
  EXPECT_TRUE((Same<struct t_vpi_time*, p_vpi_time>()));
  EXPECT_TRUE((Same<PLI_INT32, decltype(s_vpi_time::type)>()));
  EXPECT_TRUE((Same<PLI_UINT32, decltype(s_vpi_time::high)>()));
  EXPECT_TRUE((Same<PLI_UINT32, decltype(s_vpi_time::low)>()));
  EXPECT_TRUE((Same<double, decltype(s_vpi_time::real)>()));
  EXPECT_EQ(offsetof(s_vpi_time, type), 0u);
  EXPECT_LT(offsetof(s_vpi_time, type), offsetof(s_vpi_time, high));
  EXPECT_LT(offsetof(s_vpi_time, high), offsetof(s_vpi_time, low));
  EXPECT_LT(offsetof(s_vpi_time, low), offsetof(s_vpi_time, real));
}

TEST(VpiStructures, TheDelayStructureIsTheListings) {
  EXPECT_TRUE((Same<struct t_vpi_delay, s_vpi_delay>()));
  EXPECT_TRUE((Same<struct t_vpi_delay*, p_vpi_delay>()));
  EXPECT_TRUE((Same<t_vpi_time*, decltype(s_vpi_delay::da)>()));
  EXPECT_TRUE((Same<PLI_INT32, decltype(s_vpi_delay::no_of_delays)>()));
  EXPECT_TRUE((Same<PLI_INT32, decltype(s_vpi_delay::time_type)>()));
  EXPECT_TRUE((Same<PLI_INT32, decltype(s_vpi_delay::mtm_flag)>()));
  EXPECT_TRUE((Same<PLI_INT32, decltype(s_vpi_delay::append_flag)>()));
  EXPECT_TRUE((Same<PLI_INT32, decltype(s_vpi_delay::pulsere_flag)>()));
  EXPECT_EQ(offsetof(s_vpi_delay, da), 0u);
  EXPECT_LT(offsetof(s_vpi_delay, da), offsetof(s_vpi_delay, no_of_delays));
  EXPECT_LT(offsetof(s_vpi_delay, no_of_delays),
            offsetof(s_vpi_delay, time_type));
  EXPECT_LT(offsetof(s_vpi_delay, time_type), offsetof(s_vpi_delay, mtm_flag));
  EXPECT_LT(offsetof(s_vpi_delay, mtm_flag),
            offsetof(s_vpi_delay, append_flag));
  EXPECT_LT(offsetof(s_vpi_delay, append_flag),
            offsetof(s_vpi_delay, pulsere_flag));
}

TEST(VpiStructures, TheVectorValueStructureIsTheListings) {
  EXPECT_TRUE((Same<struct t_vpi_vecval, s_vpi_vecval>()));
  EXPECT_TRUE((Same<struct t_vpi_vecval*, p_vpi_vecval>()));
  EXPECT_TRUE((Same<PLI_UINT32, decltype(s_vpi_vecval::aval)>()));
  EXPECT_TRUE((Same<PLI_UINT32, decltype(s_vpi_vecval::bval)>()));
  EXPECT_EQ(offsetof(s_vpi_vecval, aval), 0u);
  EXPECT_LT(offsetof(s_vpi_vecval, aval), offsetof(s_vpi_vecval, bval));
  EXPECT_EQ(sizeof(s_vpi_vecval), 2 * sizeof(PLI_UINT32));
}

TEST(VpiStructures, TheStrengthValueStructureIsTheListings) {
  EXPECT_TRUE((Same<struct t_vpi_strengthval, s_vpi_strengthval>()));
  EXPECT_TRUE((Same<struct t_vpi_strengthval*, p_vpi_strengthval>()));
  EXPECT_TRUE((Same<PLI_INT32, decltype(s_vpi_strengthval::logic)>()));
  EXPECT_TRUE((Same<PLI_INT32, decltype(s_vpi_strengthval::s0)>()));
  EXPECT_TRUE((Same<PLI_INT32, decltype(s_vpi_strengthval::s1)>()));
  EXPECT_EQ(offsetof(s_vpi_strengthval, logic), 0u);
  EXPECT_LT(offsetof(s_vpi_strengthval, logic),
            offsetof(s_vpi_strengthval, s0));
  EXPECT_LT(offsetof(s_vpi_strengthval, s0), offsetof(s_vpi_strengthval, s1));
}

TEST(VpiStructures, TheSystemTaskStructureIsTheListings) {
  EXPECT_TRUE((Same<struct t_vpi_systf_data, s_vpi_systf_data>()));
  EXPECT_TRUE((Same<struct t_vpi_systf_data*, p_vpi_systf_data>()));
  EXPECT_TRUE((Same<PLI_INT32, decltype(s_vpi_systf_data::type)>()));
  EXPECT_TRUE((Same<PLI_INT32, decltype(s_vpi_systf_data::sysfunctype)>()));
  EXPECT_TRUE((Same<PLI_BYTE8*, decltype(s_vpi_systf_data::tfname)>()));
  EXPECT_TRUE(
      (Same<PLI_INT32 (*)(PLI_BYTE8*), decltype(s_vpi_systf_data::calltf)>()));
  EXPECT_TRUE((Same<PLI_INT32 (*)(PLI_BYTE8*),
                    decltype(s_vpi_systf_data::compiletf)>()));
  EXPECT_TRUE(
      (Same<PLI_INT32 (*)(PLI_BYTE8*), decltype(s_vpi_systf_data::sizetf)>()));
  EXPECT_TRUE((Same<PLI_BYTE8*, decltype(s_vpi_systf_data::user_data)>()));
  EXPECT_EQ(offsetof(s_vpi_systf_data, type), 0u);
  EXPECT_LT(offsetof(s_vpi_systf_data, type),
            offsetof(s_vpi_systf_data, sysfunctype));
  EXPECT_LT(offsetof(s_vpi_systf_data, sysfunctype),
            offsetof(s_vpi_systf_data, tfname));
  EXPECT_LT(offsetof(s_vpi_systf_data, tfname),
            offsetof(s_vpi_systf_data, calltf));
  EXPECT_LT(offsetof(s_vpi_systf_data, calltf),
            offsetof(s_vpi_systf_data, compiletf));
  EXPECT_LT(offsetof(s_vpi_systf_data, compiletf),
            offsetof(s_vpi_systf_data, sizetf));
  EXPECT_LT(offsetof(s_vpi_systf_data, sizetf),
            offsetof(s_vpi_systf_data, user_data));
}

TEST(VpiStructures, TheExecutionInformationStructureIsTheListings) {
  EXPECT_TRUE((Same<struct t_vpi_vlog_info, s_vpi_vlog_info>()));
  EXPECT_TRUE((Same<struct t_vpi_vlog_info*, p_vpi_vlog_info>()));
  EXPECT_TRUE((Same<PLI_INT32, decltype(s_vpi_vlog_info::argc)>()));
  EXPECT_TRUE((Same<PLI_BYTE8**, decltype(s_vpi_vlog_info::argv)>()));
  EXPECT_TRUE((Same<PLI_BYTE8*, decltype(s_vpi_vlog_info::product)>()));
  EXPECT_TRUE((Same<PLI_BYTE8*, decltype(s_vpi_vlog_info::version)>()));
  EXPECT_EQ(offsetof(s_vpi_vlog_info, argc), 0u);
  EXPECT_LT(offsetof(s_vpi_vlog_info, argc), offsetof(s_vpi_vlog_info, argv));
  EXPECT_LT(offsetof(s_vpi_vlog_info, argv),
            offsetof(s_vpi_vlog_info, product));
  EXPECT_LT(offsetof(s_vpi_vlog_info, product),
            offsetof(s_vpi_vlog_info, version));
}

TEST(VpiStructures, TheErrorInformationStructureIsTheListings) {
  EXPECT_TRUE((Same<struct t_vpi_error_info, s_vpi_error_info>()));
  EXPECT_TRUE((Same<struct t_vpi_error_info*, p_vpi_error_info>()));
  EXPECT_TRUE((Same<PLI_INT32, decltype(s_vpi_error_info::state)>()));
  EXPECT_TRUE((Same<PLI_INT32, decltype(s_vpi_error_info::level)>()));
  EXPECT_TRUE((Same<PLI_BYTE8*, decltype(s_vpi_error_info::message)>()));
  EXPECT_TRUE((Same<PLI_BYTE8*, decltype(s_vpi_error_info::product)>()));
  EXPECT_TRUE((Same<PLI_BYTE8*, decltype(s_vpi_error_info::code)>()));
  EXPECT_TRUE((Same<PLI_BYTE8*, decltype(s_vpi_error_info::file)>()));
  EXPECT_TRUE((Same<PLI_INT32, decltype(s_vpi_error_info::line)>()));
  EXPECT_EQ(offsetof(s_vpi_error_info, state), 0u);
  EXPECT_LT(offsetof(s_vpi_error_info, state),
            offsetof(s_vpi_error_info, level));
  EXPECT_LT(offsetof(s_vpi_error_info, level),
            offsetof(s_vpi_error_info, message));
  EXPECT_LT(offsetof(s_vpi_error_info, message),
            offsetof(s_vpi_error_info, product));
  EXPECT_LT(offsetof(s_vpi_error_info, product),
            offsetof(s_vpi_error_info, code));
  EXPECT_LT(offsetof(s_vpi_error_info, code), offsetof(s_vpi_error_info, file));
  EXPECT_LT(offsetof(s_vpi_error_info, file), offsetof(s_vpi_error_info, line));
}

TEST(VpiStructures, TheCallbackStructureIsTheListings) {
  EXPECT_TRUE((Same<struct t_cb_data, s_cb_data>()));
  EXPECT_TRUE((Same<struct t_cb_data*, p_cb_data>()));
  EXPECT_TRUE((Same<PLI_INT32, decltype(s_cb_data::reason)>()));
  EXPECT_TRUE((Same<PLI_INT32 (*)(t_cb_data*), decltype(s_cb_data::cb_rtn)>()));
  EXPECT_TRUE((Same<vpiHandle, decltype(s_cb_data::obj)>()));
  EXPECT_TRUE((Same<p_vpi_time, decltype(s_cb_data::time)>()));
  EXPECT_TRUE((Same<p_vpi_value, decltype(s_cb_data::value)>()));
  EXPECT_TRUE((Same<PLI_INT32, decltype(s_cb_data::index)>()));
  EXPECT_TRUE((Same<PLI_BYTE8*, decltype(s_cb_data::user_data)>()));
  EXPECT_EQ(offsetof(s_cb_data, reason), 0u);
  EXPECT_LT(offsetof(s_cb_data, reason), offsetof(s_cb_data, cb_rtn));
  EXPECT_LT(offsetof(s_cb_data, cb_rtn), offsetof(s_cb_data, obj));
  EXPECT_LT(offsetof(s_cb_data, obj), offsetof(s_cb_data, time));
  EXPECT_LT(offsetof(s_cb_data, time), offsetof(s_cb_data, value));
  EXPECT_LT(offsetof(s_cb_data, value), offsetof(s_cb_data, index));
  EXPECT_LT(offsetof(s_cb_data, index), offsetof(s_cb_data, user_data));
}

TEST(VpiStructures, TheGenericValueStructureIsTheListings) {
  EXPECT_TRUE((Same<struct t_vpi_value, s_vpi_value>()));
  EXPECT_TRUE((Same<struct t_vpi_value*, p_vpi_value>()));
  EXPECT_TRUE((Same<PLI_INT32, decltype(s_vpi_value::format)>()));
  using Arms = decltype(s_vpi_value::value);
  EXPECT_TRUE(std::is_union_v<Arms>);
  EXPECT_TRUE((Same<PLI_BYTE8*, decltype(Arms::str)>()));
  EXPECT_TRUE((Same<PLI_INT32, decltype(Arms::scalar)>()));
  EXPECT_TRUE((Same<PLI_INT32, decltype(Arms::integer)>()));
  EXPECT_TRUE((Same<double, decltype(Arms::real)>()));
  EXPECT_TRUE((Same<t_vpi_time*, decltype(Arms::time)>()));
  EXPECT_TRUE((Same<t_vpi_vecval*, decltype(Arms::vector)>()));
  EXPECT_TRUE((Same<t_vpi_strengthval*, decltype(Arms::strength)>()));
  EXPECT_TRUE((Same<PLI_BYTE8*, decltype(Arms::misc)>()));
  EXPECT_EQ(offsetof(s_vpi_value, format), 0u);
  EXPECT_LT(offsetof(s_vpi_value, format), offsetof(s_vpi_value, value));
  EXPECT_EQ(sizeof(Arms), sizeof(void*));
}

TEST(VpiStructures, TheArrayValueStructureIsTheListings) {
  EXPECT_TRUE((Same<struct t_vpi_arrayvalue, s_vpi_arrayvalue>()));
  EXPECT_TRUE((Same<struct t_vpi_arrayvalue*, p_vpi_arrayvalue>()));
  EXPECT_TRUE((Same<PLI_UINT32, decltype(s_vpi_arrayvalue::format)>()));
  EXPECT_TRUE((Same<PLI_UINT32, decltype(s_vpi_arrayvalue::flags)>()));
  using Arms = decltype(s_vpi_arrayvalue::value);
  EXPECT_TRUE(std::is_union_v<Arms>);
  EXPECT_TRUE((Same<PLI_INT32*, decltype(Arms::integers)>()));
  EXPECT_TRUE((Same<PLI_INT16*, decltype(Arms::shortints)>()));
  EXPECT_TRUE((Same<PLI_INT64*, decltype(Arms::longints)>()));
  EXPECT_TRUE((Same<PLI_BYTE8*, decltype(Arms::rawvals)>()));
  EXPECT_TRUE((Same<t_vpi_vecval*, decltype(Arms::vectors)>()));
  EXPECT_TRUE((Same<t_vpi_time*, decltype(Arms::times)>()));
  EXPECT_TRUE((Same<double*, decltype(Arms::reals)>()));
  EXPECT_TRUE((Same<float*, decltype(Arms::shortreals)>()));
  EXPECT_EQ(offsetof(s_vpi_arrayvalue, format), 0u);
  EXPECT_LT(offsetof(s_vpi_arrayvalue, format),
            offsetof(s_vpi_arrayvalue, flags));
  EXPECT_LT(offsetof(s_vpi_arrayvalue, flags),
            offsetof(s_vpi_arrayvalue, value));
  EXPECT_EQ(sizeof(Arms), sizeof(void*));
}

TEST(VpiStructures, ThePositionalInitializersFillTheFirstArms) {
  char text[] = "1010";
  s_vpi_value value = {vpiBinStrVal, {text}};
  EXPECT_EQ(value.value.str, text);
  PLI_INT32 numbers[] = {3, 5};
  s_vpi_arrayvalue array = {vpiIntVal, vpiUserAllocFlag, {numbers}};
  EXPECT_EQ(array.value.integers, numbers);
}

}  // namespace
