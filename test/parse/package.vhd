package one is
    type my_int is range 0 to 100;  
end package;

-------------------------------------------------------------------------------

use work.one.all;

package two is
    subtype my_int2 is my_int1 range 10 to 50;
end package two;
