
shepherd: shepherd.c
	cc -o shepherd shepherd.c -static
#	cc -o shepherd shepherd.c -lcpuset
clean:
	rm shepherd
