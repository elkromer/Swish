namespace eval Crypto {
    # functions that implement useful mathmatical algorithms used in cryptography
    # Auth: Reese Krome
    
    namespace eval RSA {
        # functions that implement RSA math and primality tests
        # simple encryption and decryption with non-standard key formats

        # num is a randomly selected number that will be checked for primality
        variable num 0
        variable pubkey {}
        variable prvkey {}
        

        proc getpubkey {} {
            variable pubkey
            return $pubkey
        }
        proc getprvkey {} {
            variable prvkey
            return $prvkey
        }
        proc setprime {prime} {
            # set the global prime variable
            variable num
            set num $prime
        }
        proc miller-rabin {max witnesscounter} {
            # An implementation of the Miller-Rabin primality test 
            #    max: the maximum number of base 2 factors to find
            #    witnesscounter: the maximum number of witnesses to find

            variable num
            variable basecounter 0
            variable d 0
            variable r 0

            set n [expr {$num - 1}]

            # find base 2 factors of (unknown prime - 1)
            for {set idx 1} {$idx < $max} {incr idx} {
                if {[expr {$n % (2 ** $idx) == 0}]} {
                    set d [expr { $n / (2**$idx) }]
                    set r $idx
                    # puts "$n has a factor 2^$r * $d"
                    # a base 2 factor has been found
                    incr basecounter
                }
            }
            # puts "\$n = $n\n\$d = $d\n\$r = $r"
            
            if {[expr $basecounter == 0]} {
                # if no base 2 factors, check if its a perfect square
                if {[isperfectsquare $n]} {
                    return {composite}
                }
            }

            # puts "Entering WitnessLoop"
            for {set k 0} {$k < $witnesscounter} {incr k} {
                variable x
                set a [Crypto::randrange 2 [expr $num - 2]]
                set x [expr { $a ** $d % $num } ]
                # puts "$a ** $d % $num = $x"
                if {[expr {$x == 1 || $x == $n}]} {
                    continue
                }

                # for the number of found base 2 factors
                for {set index 0} {$index < $basecounter} {incr index} {
                    variable x
                    # puts "($a ^ $d mod $num) = $x"
                    set x [expr { $x ** 2 % $num }]
                    if {[expr { $x == $n}]} { 
                        # if the continued squaring of x, mod num 
                        # returns num-1 or 1, then num is probably prime or 'a' is a strong liar
                        break
                    }
                    # if the continued squaring of x, mod num
                    # returns [2,num-2], then 'a' is a witness for the compositeness of num 
                    # and previous 'a's were in fact strong liars
                    puts "$a is a witness to the compositeness of $num. "
                    return {composite}
                }
            }
            return {num is probably prime}

        }
        proc trialdivision {max} {
            # check if the number has small prime factors
            # returns 1 if the number is divisible by small numbers
            variable num

            for {set idx 2} {$idx < $max} {incr idx} {
                if {[expr {$num % $idx == 0}]} {
                    return 1;
                }
            }
            return 0;
        }
        proc isprime {value} {
            # Based on the Baillie–PSW primality test
            # Lucas pseudoprimes have not been implemented but this does an OK job

            variable num
            set num $value

            # Try trial division up to 99 for efficiency. If not small factors are found, do a primality test
            if {[trialdivision 99]} {
                return {composite}
            } else {
                return [miller-rabin 4 10]
            }
        }
        proc test-primes {} {
            # tests each number in the list and tests primality
            # requires a file with a space separated list of primes 

            set primes [gets [open {./primes.txt}]]
            foreach prime $primes {
                puts [isprime $prime]
            }
        }
        proc rsa-encrypt-decrypt-test {} {
            # generate keys 
            rsa-keygen
            variable pubkey 
            variable prvkey
            puts $pubkey
            puts $prvkey

            # set the input data
            cd ..
            set plaintext [gets [open {./inputmessage.txt}]]
            puts "input data: $plaintext"

            set strlen [string length $plaintext]
            set plainnumeric {}
            set ciphertext {}
            set numericcipher {}
            set numericplain {}
            set outputmessage {}

            for {set index 0} {$index < $strlen} {incr index} {
                lappend plainnumeric [scan [string index $plaintext $index] %c ]
            }
            puts "numeric input data: $plainnumeric"

            foreach element $plainnumeric {
                # m^e mod n
                lappend numericcipher [expr (int($element) ** [lindex $pubkey 0]) % [lindex $pubkey 1]]
            }
            puts "numeric cipher data: $numericcipher"

            for {set index 0} {$index < $strlen} {incr index} {
                lappend ciphertext [binary format c* [lindex $numericcipher $index]]
            }
            set joinedtext [join $ciphertext ""]
            puts "cipher text: $joinedtext"

            foreach element $numericcipher {
                # c^d mod n
                lappend numericplain [expr (int($element) ** [lindex $prvkey 0]) % [lindex $prvkey 1]]
            }
            puts "decrypted numeric data: $numericplain"

            for {set index 0} {$index < $strlen} {incr index} {
                lappend outputmessage [binary format c* [lindex $numericplain $index]]
            }
            set joinedtext [join $outputmessage ""]
            puts "plain text: $joinedtext"
        }
        proc rsa-keygen {} {
            # computes RSA keys as per Burt Kaliski at RSA Labs
            # http://www.mathaware.org/mam/06/Kaliski.pdf

            # tries to select large primes p and q
            # computes n as pq
            # computes e to be coprime with p-1, q-1
                # sometimes fails at this
            # computes d to be the modular inverse of e mod n
            # sets the pubkey variable to be e, n
            # sets the prvkey variable to be d, n

            set prand [Crypto::randrange 100 300]
            set qrand [Crypto::randrange 100 300]

            # check if the number is prime, if compositie try again
            while {[isprime $prand] eq {composite}} {
                set prand [Crypto::randrange 100 300]
            }

            while {[isprime $qrand] eq {composite}} {
                set qrand [Crypto::randrange 100 300]
            }

            set n [expr $prand * $qrand]

            # puts "p: $prand q: $qrand n: $n"

            # select an odd public exponent between 3, n-1 
            # that is relatively prime to p-1 and q-1

            set e [Crypto::randrange 3 [expr $n - 1]]

            # pick random values for e until an e is found that is coprime to p-1, q-1
            while {[Crypto::gcd $e [expr $prand - 1]] != 1} {
                set e [Crypto::randrange 3 [expr $n - 1]]
            }

            if {[Crypto::gcd $e [expr $qrand - 1]] != 1} {
                puts {critical failure: e was not coprime with q. try again}
                return;
            }

            # puts "p: $prand q: $qrand n: $n e: $e"

            # compute L to be the least common multiple of p-1, q-1
            # de ≡ 1 ( mod L )
            set L [Crypto::lcm [expr $prand - 1] [expr $qrand - 1]]
            puts "p: $prand q: $qrand n: $n e: $e L: $L"

            # compute d to be the modular inverse of e mod L
            set d [Crypto::modInv $e $L] 

            # puts "p: $prand q: $qrand n: $n e: $e L: $L d: $d"
            
            # e*d mod L should be 1
            # puts [expr ($e * $d % $L)]

            variable pubkey
            variable prvkey
            set pubkey "$e $n"
            set prvkey "$d $n"

        }
    }

    proc isperfectsquare {testnumber} {
        # check if a number is a perfect square
        variable square
        set square [::tcl::mathfunc::sqrt $testnumber]
        return [expr abs($square - int($square)) > 0 ? 0 : 1]
    } 
    proc gcd {p q} {
        while 1 {
            if {![set p [expr {$p % $q}]]} {return [expr { $q>0 ? $q : -$q }]}
            if {![set q [expr {$q % $p}]]} {return [expr { $p>0 ? $p : -$p }]}
        }
    } 
    proc gcdExt {a b} {
        if {$b == 0} {
            return [list 1 0 $a]
        }
        set q [expr {$a / $b}]
        set r [expr {$a % $b}]
        lassign [gcdExt $b $r] s t g
        return [list $t [expr {$s - $q*$t}] $g]
    }
    proc modInv {a m} {
        lassign [gcdExt $a $m] i -> g
        if {$g != 1} {
            return -code error "no inverse exists of $a %! $m"
        }
        while {$i < 0} {
            incr i $m
        }
        return $i
    }
    proc lcm {p q} {
        set m [expr {$p * $q}]
        if {!$m} {return 0}
        while 1 {
            set p [expr {$p % $q}]
            if {!$p} { return [expr {$m / $q}] }
            set q [expr {$q % $p}]
            if {!$q} { return [expr {$m / $p}] }
        }
    } 
    proc randrange {min max} { 
        # get a random number within a range
        return [expr {int(rand()*($max - $min + 1)) + $min}] 
    }             
} 


Crypto::RSA::rsa-encrypt-decrypt-test