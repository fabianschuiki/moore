// RUN: moore %s

// See IEEE 1800-2017 §35.5.4

import "DPI" function void myInit();
import "DPI-C" function void myInit2();

import "DPI-C" pure function real sin(real);

import "DPI-C" function chandle malloc(int size); // standard C function
import "DPI-C" function void free(chandle ptr); // standard C function

import "DPI-C" function chandle newQueue(input string name_of_queue);

import "DPI-C" newQueue = function chandle newAnonQueue(input string s = null);
import "DPI-C" function chandle newElem(bit [15:0]);
import "DPI-C" function void enqueue(chandle queue, chandle elem);
import "DPI-C" function chandle dequeue(chandle queue);

import "DPI-C" function bit [15:0] getStimulus();
import "DPI-C" context function void processTransaction(chandle elem, output logic [64:1] arr [0:63]);
import "DPI-C" task checkResults(input string s, bit [511:0] packet);

// See IEEE 1800-2017 §H.10.2

typedef struct {int x; int y;} pair;
typedef struct {int a; bit [6:1][1:8] b [65:2]; int c;} triple;

import "DPI-C" function void f1(input int i1, pair i2, output logic [63:0] o3);
import "DPI-C" function void f2(input triple t);
export "DPI-C" function f3;
export "DPI-C" function f4;

function void f3(input int i, output int o [0:7]);
endfunction

function void f4(input int i, output logic [63:0] o);
endfunction
