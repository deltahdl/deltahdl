/*
 * vpi_compatibility.h -- the compatibility-mode file of the IEEE Std
 * 1800-2023 Verification Procedural Interface (VPI), Annex L.
 *
 * vpi_user.h includes this file. User application code does not.
 *
 * The macro definitions here are what the SystemVerilog PLI implements its
 * backwards compatibility modes with.
 *
 * §L.2 shows this file, and this is it as the annex shows it: a file that
 * is read once per translation unit, by vpi_user.h ahead of the routine
 * declarations the definitions below rename, and that rejects a second
 * reading rather than ignoring it -- VPI_COMPATIBILITY_H is not an include
 * guard but the mark of the first reading, which the #error at the top
 * tests for. §L.1 says why: the file supports the compatibility mode
 * functionality of §36.12, especially §36.12.2.1, and user application code
 * selects a mode by defining one VPI_COMPATIBILITY_VERSION_ symbol as 1 (or
 * with -D) before including vpi_user.h, and includes nothing else.
 *
 * The one place this file departs from the annex's text is the value the
 * chained symbol is given. The annex writes the two chaining definitions
 * with no value, and then tests the chained symbol with #elif, which is
 * ill-formed for a symbol that expands to nothing ("expected value in
 * expression"), so the 1800v2017 and 1800v2023 modes as the annex writes
 * them fail to compile. The chained symbol is defined as 1 here, the value
 * §36.12.2.1 has the application give the symbol it selects, and the modes
 * resolve to 1800v2012 as the annex intends.
 *
 * The branches below test the symbols by value, so a symbol selects a mode
 * only when it expands to something true, and each branch rejects only the
 * versions with branches of their own. 1800v2017 selected beside 1800v2023
 * is therefore not rejected: both chain onto 1800v2012, whose branch finds
 * no other version selected. That is narrower than the sentence of
 * §36.12.2.1 that promises a compilation error for more than one symbol,
 * and it is what the annex's listing does.
 */
#ifdef VPI_COMPATIBILITY_H
#error \
    "The vpi_compatibility.h file can only be included by vpi_user.h directly."
#endif
#define VPI_COMPATIBILITY_H
/* Compatibility-mode variants of functions */
#if VPI_COMPATIBILITY_VERSION_1800v2023
#define VPI_COMPATIBILITY_VERSION_1800v2012 1
#endif
#if VPI_COMPATIBILITY_VERSION_1800v2017
#define VPI_COMPATIBILITY_VERSION_1800v2012 1
#endif

#if VPI_COMPATIBILITY_VERSION_1364v1995
#if VPI_COMPATIBILITY_VERSION_1364v2001 || \
    VPI_COMPATIBILITY_VERSION_1364v2005 || \
    VPI_COMPATIBILITY_VERSION_1800v2005 || \
    VPI_COMPATIBILITY_VERSION_1800v2009 || VPI_COMPATIBILITY_VERSION_1800v2012
#error "Only one VPI_COMPATIBILITY_VERSION symbol definition is allowed."
#endif
#define vpi_compare_objects vpi_compare_objects_1364v1995
#define vpi_control vpi_control_1364v1995
#define vpi_get vpi_get_1364v1995
#define vpi_get_str vpi_get_str_1364v1995
#define vpi_get_value vpi_get_value_1364v1995
#define vpi_handle vpi_handle_1364v1995
#define vpi_handle_by_index vpi_handle_by_index_1364v1995
#define vpi_handle_by_multi_index vpi_handle_by_multi_index_1364v1995
#define vpi_handle_by_name vpi_handle_by_name_1364v1995
#define vpi_handle_multi vpi_handle_multi_1364v1995
#define vpi_iterate vpi_iterate_1364v1995
#define vpi_put_value vpi_put_value_1364v1995
#define vpi_register_cb vpi_register_cb_1364v1995
#define vpi_scan vpi_scan_1364v1995
#elif VPI_COMPATIBILITY_VERSION_1364v2001
#if VPI_COMPATIBILITY_VERSION_1364v1995 || \
    VPI_COMPATIBILITY_VERSION_1364v2005 || \
    VPI_COMPATIBILITY_VERSION_1800v2005 || \
    VPI_COMPATIBILITY_VERSION_1800v2009 || VPI_COMPATIBILITY_VERSION_1800v2012
#error "Only one VPI_COMPATIBILITY_VERSION symbol definition is allowed."
#endif
#define vpi_compare_objects vpi_compare_objects_1364v2001
#define vpi_control vpi_control_1364v2001
#define vpi_get vpi_get_1364v2001
#define vpi_get_str vpi_get_str_1364v2001
#define vpi_get_value vpi_get_value_1364v2001
#define vpi_handle vpi_handle_1364v2001
#define vpi_handle_by_index vpi_handle_by_index_1364v2001
#define vpi_handle_by_multi_index vpi_handle_by_multi_index_1364v2001
#define vpi_handle_by_name vpi_handle_by_name_1364v2001
#define vpi_handle_multi vpi_handle_multi_1364v2001
#define vpi_iterate vpi_iterate_1364v2001
#define vpi_put_value vpi_put_value_1364v2001
#define vpi_register_cb vpi_register_cb_1364v2001
#define vpi_scan vpi_scan_1364v2001
#elif VPI_COMPATIBILITY_VERSION_1364v2005
#if VPI_COMPATIBILITY_VERSION_1364v1995 || \
    VPI_COMPATIBILITY_VERSION_1364v2001 || \
    VPI_COMPATIBILITY_VERSION_1800v2005 || \
    VPI_COMPATIBILITY_VERSION_1800v2009 || VPI_COMPATIBILITY_VERSION_1800v2012
#error "Only one VPI_COMPATIBILITY_VERSION symbol definition is allowed."
#endif
#define vpi_compare_objects vpi_compare_objects_1364v2005
#define vpi_control vpi_control_1364v2005
#define vpi_get vpi_get_1364v2005
#define vpi_get_str vpi_get_str_1364v2005
#define vpi_get_value vpi_get_value_1364v2005
#define vpi_handle vpi_handle_1364v2005
#define vpi_handle_by_index vpi_handle_by_index_1364v2005
#define vpi_handle_by_multi_index vpi_handle_by_multi_index_1364v2005
#define vpi_handle_by_name vpi_handle_by_name_1364v2005
#define vpi_handle_multi vpi_handle_multi_1364v2005
#define vpi_iterate vpi_iterate_1364v2005
#define vpi_put_value vpi_put_value_1364v2005
#define vpi_register_cb vpi_register_cb_1364v2005
#define vpi_scan vpi_scan_1364v2005
#elif VPI_COMPATIBILITY_VERSION_1800v2005
#if VPI_COMPATIBILITY_VERSION_1364v1995 || \
    VPI_COMPATIBILITY_VERSION_1364v2001 || \
    VPI_COMPATIBILITY_VERSION_1364v2005 || \
    VPI_COMPATIBILITY_VERSION_1800v2009 || VPI_COMPATIBILITY_VERSION_1800v2012
#error "Only one VPI_COMPATIBILITY_VERSION symbol definition is allowed."
#endif
#define vpi_compare_objects vpi_compare_objects_1800v2005
#define vpi_control vpi_control_1800v2005
#define vpi_get vpi_get_1800v2005
#define vpi_get_str vpi_get_str_1800v2005
#define vpi_get_value vpi_get_value_1800v2005
#define vpi_handle vpi_handle_1800v2005
#define vpi_handle_by_index vpi_handle_by_index_1800v2005
#define vpi_handle_by_multi_index vpi_handle_by_multi_index_1800v2005
#define vpi_handle_by_name vpi_handle_by_name_1800v2005
#define vpi_handle_multi vpi_handle_multi_1800v2005
#define vpi_iterate vpi_iterate_1800v2005
#define vpi_put_value vpi_put_value_1800v2005
#define vpi_register_cb vpi_register_cb_1800v2005
#define vpi_scan vpi_scan_1800v2005
#elif VPI_COMPATIBILITY_VERSION_1800v2009
#if VPI_COMPATIBILITY_VERSION_1364v1995 || \
    VPI_COMPATIBILITY_VERSION_1364v2001 || \
    VPI_COMPATIBILITY_VERSION_1364v2005 || \
    VPI_COMPATIBILITY_VERSION_1800v2005 || VPI_COMPATIBILITY_VERSION_1800v2012
#error "Only one VPI_COMPATIBILITY_VERSION symbol definition is allowed."
#endif
#define vpi_compare_objects vpi_compare_objects_1800v2009
#define vpi_control vpi_control_1800v2009
#define vpi_get vpi_get_1800v2009
#define vpi_get_str vpi_get_str_1800v2009
#define vpi_get_value vpi_get_value_1800v2009
#define vpi_handle vpi_handle_1800v2009
#define vpi_handle_by_index vpi_handle_by_index_1800v2009
#define vpi_handle_by_multi_index vpi_handle_by_multi_index_1800v2009
#define vpi_handle_by_name vpi_handle_by_name_1800v2009
#define vpi_handle_multi vpi_handle_multi_1800v2009
#define vpi_iterate vpi_iterate_1800v2009
#define vpi_put_value vpi_put_value_1800v2009
#define vpi_register_cb vpi_register_cb_1800v2009
#define vpi_scan vpi_scan_1800v2009
#elif VPI_COMPATIBILITY_VERSION_1800v2012
#if VPI_COMPATIBILITY_VERSION_1364v1995 || \
    VPI_COMPATIBILITY_VERSION_1364v2001 || \
    VPI_COMPATIBILITY_VERSION_1364v2005 || \
    VPI_COMPATIBILITY_VERSION_1800v2005 || VPI_COMPATIBILITY_VERSION_1800v2009
#error "Only one VPI_COMPATIBILITY_VERSION symbol definition is allowed."
#endif
#define vpi_compare_objects vpi_compare_objects_1800v2012
#define vpi_control vpi_control_1800v2012
#define vpi_get vpi_get_1800v2012
#define vpi_get_str vpi_get_str_1800v2012
#define vpi_get_value vpi_get_value_1800v2012
#define vpi_handle vpi_handle_1800v2012
#define vpi_handle_by_index vpi_handle_by_index_1800v2012
#define vpi_handle_by_multi_index vpi_handle_by_multi_index_1800v2012
#define vpi_handle_by_name vpi_handle_by_name_1800v2012
#define vpi_handle_multi vpi_handle_multi_1800v2012
#define vpi_iterate vpi_iterate_1800v2012
#define vpi_put_value vpi_put_value_1800v2012
#define vpi_register_cb vpi_register_cb_1800v2012
#define vpi_scan vpi_scan_1800v2012
#endif
