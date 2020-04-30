// Copyright (c) 2016-2020 Fabian Schuiki
mod common;
use crate::common::*;

#[test]
fn timeunit_stmt() {
    parse("timeunit 1ns/1ps;");
}
