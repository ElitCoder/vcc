after to ssa
   1     0    label   $L4
	   6     1    mov     3         $27
	   7     3    mov     6         $28
	  25     6    ba      0         $L8
	  25     7    ba      $L7
  25    12    label   $L8
	  15    13    mov     4         $41
	  22    15    ba      $L14
  22    30    label   $L14
	  22    45    phi     $46 := ($41, $52)
	  22    51    phi     $45 := ($19, $49)
	  17    31    slt     $46       $28       $47
	  22    32    bt      $47       $L13
	  22    33    ba      $L15
  22    16    label   $L13
	  20    17    ba      $L17
  20    22    label   $L17
	  20    44    phi     $50 := ($46, $53)
	  18    23    slt     $50       $28       $51
	  20    24    bt      $51       $L16
	  20    25    ba      $L18
  20    18    label   $L16
	  19    19    add     $50       1         $53
	  20    21    ba      $L17
  20    26    label   $L18
	  21    27    add     $50       2         $52
	  22    29    ba      $L14
  22    34    label   $L15
	  24    35    ba      L5
  28    38    label   L5
	  28    47    phi     $37 := ($30, $28)
	  28    46    phi     $38 := ($27, $46)
	  28    52    phi     $34 := ($19, $45)
	  28    39    add     $38       $37       $39
	  30    41    put     $39
	  32    42    mov     0         $40
	  32    43    ret     $40
  25     8    label   $L7
	  10     9    mov     3         $30
	  11    11    ba      L5




int main() {
	int a;
	int b;
	int c;

	a = 3;
	b = 6;

	if(a == b) {
		b = 3;
		goto L5;
	}

	else {
		a = 4;

		while(a < b) {
			while(a < b) {
				a = a + 1;
			}
			a = a + 2;
		}
	}

L5:
	c = a + b;

	put(c);

	return 0;
}

int main() {
	int a;

	a = 3;

	while(a < 4) {
		while(a < 4) {
			a = a + 1;
		}
	}

  put(a);

	return 0;
}
