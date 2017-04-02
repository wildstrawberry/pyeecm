'''
Filename: pyeecm
Version: 1.0
Description: Factoring integer using the Elliptic Curve Method with Edwards curve 
Curves in form: a*x^2 + y^2 = 1 + d*x^2*y^2 (with DEFAULT a=1)
With Extended Coordinates, torsion-group Z/12Z by the Montgomery construction
Limit of digits: ? (limited by (int), should be fixed in future)
Acknowledgements: pyecm by Martin Kelly, Eric Larson
TODO: probably combining other coordinates in the future
History and Reference: see bottom
'''

import math
import sys
import time
import random

SMALLEST_COUNTEREXAMPLE_FASTPRIME = 2047
PRODUCT = 111546435 # 3 * 5 * 7 * 11 * 13 * 17 * 19 * 23 
VERSION = '1.0'
VERBOSE = 1
COLORED = 0

if COLORED==1:
	from termcolor import colored

try: # Use psyco if available
	import psyco
	psyco.full()
	print 'with psyco'
except ImportError:
	print 'without psyco'
	pass

try:# Use gmpy if available (otherwise define our own functions to replace its functionality)
	from gmpy import gcd, invert, mpz, next_prime
	print 'with gmpy'
except ImportError:
	print 'without gmpy'
	def gcd(a, b):

		if b == 0:
			return a
		elif a == 0:
			return b

		count = 0
	
		if a < 0:
			a = -a
		if b < 0:
			b = -b

		while not ((a & 1) | (b & 1)):
			count += 1
			a >>= 1
			b >>= 1

		while not a & 1:
			a >>= 1

		while not b & 1:
			b >>= 1

		if b > a:
			b,a = a,b

		while b != 0 and a != b:
			a -= b
			while not (a & 1):
				a >>= 1

			if b > a:
				b, a = a, b

		return a << count

	def invert(a, b):
		'''invert(a, b) --> inverse of a (mod b). 
		Computes the inverse of a modulo b. b must be odd.
		Returns the inverse of a (mod b).'''

		if a == 0 or b == 0:
			return 0

		truth = False
		if a < 0:
			t = True
			a = -a

		b_orig = b
		alpha = 1
		beta = 0

		while not a & 1:
			if alpha & 1:
				alpha += b_orig
			alpha >>= 1
			a >>= 1

		if b > a:
			a, b = b, a
			alpha, beta = beta, alpha

		while b != 0 and a != b:
			a -= b
			alpha -= beta

			while not a & 1:
				if alpha & 1:
					alpha += b_orig
				alpha >>= 1
				a >>= 1
			
			if b > a:
				a,b = b,a
				alpha, beta = beta, alpha

		if a == b:
			a -= b
			alpha -= beta
			a, b = b, a
			alpha, beta = beta, alpha

		if a != 1:
			return 0

		if truth:
			alpha = b_orig - alpha
		
		return alpha

	def mpz(n):
		return n

#M_ONE = mpz(-1) # Make sure everything works with or without gmpy
#ZERO = mpz(0)
#ONE = mpz(1)


''' Edwards curves with normal coordinates '''

def Edwards_add(p1, p2, a, d, n):
	'''Edwards_add(p1, p2, a, d, n) -> list of addition result '''

	X1, Z1, Y1, T1 = p1[0], p1[1], p1[2], p1[3]
	X2, Z2, Y2, T2 = p2[0], p2[1], p2[2], p2[3]

	X3 = (X1*Y2*Z2*T1 + X2*Y1*Z1*T2) % n
	Z3 = (Z1*Z2*T1*T2 + d*X1*X2*Y1*Y2) % n
	Y3 = (Y1*Y2*Z1*Z2 - a*X1*X2*T1*T2) % n
	T3 = (Z1*Z2*T1*T2 - d*X1*X2*Y1*Y2) % n
	return [X3, Z3, Y3, T3]

def Edwards_double(p1, a, d, n):
	'''Edwards_double(p1, a, d, n) -> list of doubling result '''

	X1, Z1, Y1, T1 = p1[0], p1[1], p1[2], p1[3]

	X3 = (X1*Y1*Z1*T1 + X1*Y1*Z1*T1) % n
	Z3 = (Z1*Z1*T1*T1 + d*X1*X1*Y1*Y1) % n
	Y3 = (Y1*Y1*Z1*Z1 - a*X1*X1*T1*T1) % n
	T3 = (Z1*Z1*T1*T1 - d*X1*X1*Y1*Y1) % n
	return [X3, Z3, Y3, T3]

def Edwards_multiply(p, degree, a, d, n):
	'''Edwards_multiply(p, degree, d, n) -> p multiplied by degree.'''

	g = 0
	count = 0
	while not degree & 1:
		degree >>= 1
		count += 1

	while degree:
		g <<= 1
		g ^= degree & 1
		degree >>= 1

	p2 = p[:]
	g >>= 1

	while g > 0:
		p = Edwards_double(p, a, d, n)
		if g & 1:
			p = Edwards_add(p, p2, a, d, n)

		g >>= 1
		for _ in xrange(count):
			p = Edwards_double(p, a, d, n)

	return p 


''' Edwards curves with extended coordinates '''

def Edwards_add_extended(p1, p2, a, n):
	'''Edwards_add_extended(p1, p2, a, n) -> list of addition result, in EXTENDED coordinates. '''

	if p1==p2:
		return Edwards_double_extended(p1, a, n)

	X1, Y1, Z1, T1 = p1[0], p1[1], p1[2], p1[3]
	X2, Y2, Z2, T2 = p2[0], p2[1], p2[2], p2[3]
	A = X1*X2
	B = Y1*Y2
	C = Z1*T2
	D = T1*Z2
	E = D+C
	F = (X1-Y1)*(X2+Y2)+B-A
	G = B+a*A
	H = D-C
	X3 = E*F
	Y3 = G*H
	T3 = E*H
	Z3 = F*G

	return [X3%n, Y3%n, Z3%n, T3%n]

def Edwards_double_extended(p1, a, n):
	'''Edwards_double_extended(p1, a, n) -> list of doubling result '''

	X1, Y1, Z1, T1 = p1[0], p1[1], p1[2], p1[3]

	A = X1**2
	B = Y1**2
	C = 2*Z1**2
	D = a*A
	E = (X1+Y1)**2-A-B
	G = D+B
	F = G-C
	H = D-B
	X3 = E*F
	Y3 = G*H
	T3 = E*H
	Z3 = F*G
	return [X3%n, Y3%n, Z3%n, T3%n]

def Edwards_multiply_extended(p, degree, a, n):
	'''Edwards_multiply_extended(p, degree, a, n) -> p multiplied by degree.'''

	g = 0
	count = 0
	while not degree & 1:
		degree >>= 1
		count += 1

	while degree:
		g <<= 1
		g ^= degree & 1
		degree >>= 1

	p2 = p[:]
	g >>= 1

	while g > 0:
		p = Edwards_double_extended(p, a, n)
		if g & 1:
			p = Edwards_add_extended(p, p2, a, n)

		g >>= 1
		for _ in xrange(count):
			p = Edwards_double_extended(p, a, n)

	return p 


''' Short_Weierstrass curves, check  http://hyperelliptic.org/EFD/g1p/auto-shortw.html for details'''

def Short_Weierstrass_add(p1, p2, a, n):
	'''Weierstrass_add(p1, p2, a, n) -> list of addition result
	Adds two points on an elliptic curve. Returns a list of the addition result.'''

	x1, y1 = p1[0], p1[1]
	x2, y2 = p2[0], p2[1]

	if x1 == x2:
		return Short_Weierstrass_double(p1, a, n)

	x2_x1=invert(x2-x1,n)
	if x2_x1==0:
		return [gcd(x2-x1,n),-1]
	else:
		l = ((y2-y1)*x2_x1) % n
		x3 = (l*l-x1-x2) % n
		y3 = (l*(x1-x3)-y1) % n

	return [x3, y3]

def Short_Weierstrass_double(p1, a, n):
	'''Weierstrass_double_projective(p1, a, n) -> list of addition result
	This is a specialized version of add, used when we know the two points are the same; therefore, we can apply some optimizations and remove some checks. double has limited use, mainly within ECM.
	Returns a list of the addition result'''

	x1, y1 = p1[0], p1[1]
	double_y1 = invert(2*y1,n)
	if double_y1==0:
		return gcd(2*y1,n)
	else:
		l = ((3*x1*x1+a)*double_y1) % n
		x3 = (l*l-2*x1) % n
		y3 = (l*(x1-x3)-y1) % n

	return [x3, y3]


def eecm(n):
	'''eecm(n) -> factors (yielded via generator)
	Factor an integer n using the (Edwards) Elliptic Curve Method.
	Yields factors of n.'''

	def mainloop(n, b):
		'''mainloop(n, b) -> factors in [b,n]'''
	
		if isprime(n):
			yield n
			return

		points = [] # A collection of points to avoid recalculation of primes
		points_new = []
		
		log_n = int(math.log(n))
		u = int( math.e ** math.sqrt ( .25 * math.log(n) * math.log ( .5 * math.log(n) ) ) ) + 1 # origin version
		log_u = int(math.log(u))
		u2 = int(u * math.log(n) / (math.log(math.log(n))**2))
		
		if (VERBOSE):
			log10_n = int(math.log(n)/math.log(10))+1
			print 'Factoring', log10_n, 'digits number', n, 'with Bound1:', u, 'Bound2:', u2
		
		''' generate curve according to Theorem 7.7, 7.8 in [1]'''
		a4_weierstrass = -12
		p0 = [-2,-4]
		p_weierstrass = [4,4]
	
		f = 1 
		contra_curvae = 0
		
		while f in (1, n):
			
			'''if non-trivial factor found on Weierstrass coordinates'''
			if(p_weierstrass[-1]==-1):
				yield p_weierstrass[0]
				n/=p_weierstrass[0]
				if (COLORED):
					print colored('find factor','green'), colored(p_weierstrass[0],'yellow'), colored('in Weierstrass curve','green')
				else:
					print 'find factor', p_weierstrass[0], 'in Weierstrass curve'
				
				if isprime(n):
					yield n
					return
				p_weierstrass = p0[:]
				if n == 1:
					return
			
			b += 1
			if b & 1:
				while not n % b:
					yield b
					n /= b
				if n == 1:
					return
			
			contra_curvae+=1
			
			s = p_weierstrass[0]
			t = p_weierstrass[1]
			p_weierstrass = Short_Weierstrass_add(p0, p_weierstrass, a4_weierstrass, n)
			
			'''parameters'''

			d = (-((s-2)**3)*((s+6)**3)*(s*s-12*s-12)*invert(1024*s*s*t*t,n))%n
			
			f = gcd(d,n)
			
			if(d==0 or d==1):
				continue
			
			x1 = (8*t*(s*s+12)) % n
			z1 = ((s-2)*(s+6)*(s*s+12*s-12)) % n
			y1 = (-4*s*(s*s-12*s-12)) % n
			t1 = ((s-2)*(s+6)*(s*s-12)) % n
			
			inv_z1 = invert(z1,n)
			inv_t1 = invert(t1,n)
		
			X1 = x1*inv_z1%n
			Y1 = y1*inv_t1%n
			p1 = [ X1 , Y1 , 1, X1*Y1%n ]
			
			prime = 3

			for _ in xrange(int(math.log(u, 2))):
				p1 = Edwards_double_extended(p1, 1, n)

			while prime < u - log_u - 2 and f in (1, n):
				product = 1
				count = 0
				while count < log_u:
					while not isprime(prime):
						prime += 2

					product *= prime ** max(1, int(math.log(u, prime)))
					prime += 2
					count += 1
				p2 = p1[:]
				
				p1 = Edwards_multiply_extended(p1, product, 1, n)

			while prime < u and f in (1, n):
				while not isprime(prime):
					prime += 2

				p2 = p1[:]
				degree =  prime ** max(1, int(math.log(u, prime)))
				p1 = Edwards_multiply_extended(p1, degree, 1, n)
				prime += 2

			if f in (1, n):
				w = p2[2]
				f = gcd(w, n)
				points.append(p2[:])
				points_new.append(p1[:])

			if len(points) >= log_n and f in (1, n):
				old_prime = prime - 2
				while prime < u2:
					product = 1
					while not isprime(prime):
						prime += 2
					for i in xrange(log_n):
						point = points[i][:]

						points_new[i] = Edwards_add_extended(points_new[i] , Edwards_multiply_extended(point, prime - old_prime, 1, n), 1, n)	
						product = product * points_new[i][2]
						product %= n

					old_prime = prime
					prime += 2
					f = gcd(n, product)

					if f not in (1, n):
						break

				points = []
				points_new = []
				
		if(VERBOSE):
			if(COLORED):
				print colored('Factor ','green'),colored(f,'yellow'),colored(' found with ','green'),colored(contra_curvae,'yellow'),colored(' curves tried.','green')
			else:
				print 'Factor', f, 'found with', contra_curvae, 'curves tried.'
		
		for factor in mainloop(f, b):
			yield factor
		for factor in mainloop(n / f, b):
			yield factor

	if not isinstance(n, int) and not isinstance(n, long):
		raise ValueError, 'Number given must be integer or long.'

	if n < 0:
		yield -1
		n = abs(n)

	u = int( math.e ** math.sqrt ( .25 * math.log(n) * math.log( .5 * math.log(n) ) ) ) + 1
	trial_division_bound = max(23, int(u / (math.log(u)**2)))

	while not n & 1:
		n >>= 1
		yield 2

	for prime in xrange(3, trial_division_bound,2): # Trial division
		while not n % prime:
			n /= prime
			yield prime

	if n == 1:
		return

	for factor in mainloop(n, trial_division_bound - 1):
		yield factor

def atdn(a, d, n):
	'''atdn(a, d, n) -> result
	Calculates a to the dth modulus n. Required sub-algorithm for ECM.
	Returns the calculation's result.'''

	x = 1
	while d > 0:
		if d & 1 == 1:
			x = (a * x) % n

		a = (a * a) % n
		d >>= 1
	
	return x

def fastprime(n): 
	'''fastprime(n) -> True or False
	Tests for primality of n using an algorithm that is very fast (O(n**3 / log(n) (assuming quadratic multiplication))  but inaccurate for n >= 2047.
	Returns the primality of n.'''

	if n <= 28: 
		if n in (2, 3, 5, 7, 11, 13, 17, 19, 23): 
			return True 
		else: 
			return False 

	if not n & 1: # Quicker than n % 2 
		return False 

	m = int(n % PRODUCT ) # not a long.
	for i in (3,5,7,11,13,17,19,23): 
		if not n % i: 
			return False 
	if n < 841: # 29 ** 2
		return True 

	for i in xrange(4, int(math.log(n)/(math.log(n) ** 2))): # trial divide up to 6 * int(math.log(n)/(math.log(n) ** 2)) - 1 
		p1 = (i << 1) + (i << 2) + 5 # 6i + 5 
		p2 = p1 + 2 
		prod = p1 * p2 
		m = n % prod 

		if not m % p1: 
			return False 
		if not m % p2: 
			return False 

		if n < (prod + (p1 << 1) + (p1 << 3) + 36): # if n < (p1 + 6)**2 
			return True 

	j = 1 
	d = n >> 1 

	while not d & 1: # Quicker than d % 2 
		d >>= 1 
		j += 1 

	count = 0 

	g = 0	 # The next few lines do a binary reversal of d
	while d: 
		g <<= 1 
		g += d & 1 
		d >>= 1 

	p = 1 
	while g: 
		p = p * p % n 
		p <<= g & 1 # Multiply p by 2 if g is odd 
		g >>= 1 
	# Now p = atdn(a, d, n). Because a = 2, we can do some tricks to speed this up.
	if p > n: 
		p -= n 

	if p == 1 or p == n - 1: 
		return True 

	while count < j - 1: 
		p = p * p % n 
		count += 1 

		if p == 1: 
			return False 
		elif p == n - 1: 
			return True 

	return False 

def isprime(n): 
	''' isprime(n) -> True or False '''
	if not fastprime(n): 
		return False 
	elif n < SMALLEST_COUNTEREXAMPLE_FASTPRIME: 
		return True 

	j = 1 
	d = n >> 1 

	while not d & 1: 
		d >>= 1 
		j += 1 

	for a in xrange(3, int(0.75 * math.log(math.log(n)) * math.log(n))): 
		if not fastprime(a): 
			continue 

		count = 0 
		do_loop = 0 
		p = atdn(a,d,n) 

		if p == 1 or p == n - 1: 
			continue 

		while count < j: 
			p = (p * p) % n 
			count += 1 

			if p == 1: 
				return False 
			elif p == n - 1: 
				do_loop = 1 
				break 

		if do_loop: 
			continue 

		return False 

	return True

def help():
	print	'''\
Usage: pyeecm [factors]...
Factor numbers using the Elliptic Curve Method with Edward Curves
With no factors given via command-line, read standard input.
Report bugs to Ravlyuchenko <ravlyuchenko@gmail.com>.'''

	sys.exit()

def command_line():
	try:
		factors = sys.argv[1:]
		try:
			factors = [int(factor) for factor in factors]
		except ValueError: # If non-int given
			help()

		first_item = True

		for factor in factors:
			if not first_item:
				print # Formatting to look right
			print	'Factoring %d:' % factor
			for factor in eecm(factor):
				print  factor 

			first_item = False

	except IndexError: # Incorrect parameters given
		help()

	sys.exit()

def interactive():
	print	'python-eecm v. %s (interactive mode):' % VERSION
	print	'Type "exit" at any time to quit.'
	print
	try:
		response = raw_input().lower().strip()
		while response != 'exit' and response != 'quit':
			try:
				n = int(response)
				print	'Factoring number %d:' % n
				start = time.time()
				for factor in eecm(n):
					if(COLORED):
						print  colored(factor,'blue')
					else:
						print factor
						
				print 'time expired:', time.time() - start
				print
			except (IndexError, ValueError):
				print	'Please enter an integer.'
			response = raw_input().lower().strip()
	except (EOFError, KeyboardInterrupt):
		sys.exit()

def main():
	
	for item in sys.argv[1:]:
		if item == '-h' or item == '--help':
			help()

	try:
		sys.argv[1]
		command_line()
	except IndexError:
		interactive()

if __name__ == '__main__':
	main()

def debug():
	start = time.time()

	u = 0
	n = 3218147

	a = -8
	p0 = [12,40]
	p_weierstrass = p0[:]
	
	while(u<5):
		u+=1
		print u, p_weierstrass
	
		s = p_weierstrass[0]
		t = p_weierstrass[1]
		p_weierstrass = Short_Weierstrass_add(p0, p_weierstrass, a, n)

		alpha = invert((t+25)*invert(s-9,n)+1,n)
		beta = (2*alpha*(4*alpha+1)*invert(8*alpha*alpha-1,n))%n
		d = ((2*(2*beta-1)*(2*beta-1)-1)*invert((2*beta-1)**4,n))%n
		
		f = gcd(d,n)
		
		if(d==0 or d==1):
			continue
			
		x1 = (2*beta-1)*(4*beta-3) % n
		z1 = (6*beta-5) % n
		y1 = (2*beta-1)*(t*t+50*t-2*s**3+27*s*s-104) % n
		t1 = (t+3*s-2)*(t+s+16) % n
	
		p1 = [ x1 , z1 , y1 , t1 ]	
			
		inv_z1 = invert(z1,n)
		inv_t1 = invert(t1,n)
		
		X1 = x1*inv_z1%n
		Y1 = y1*inv_t1%n
		p_extended = [ X1 , Y1 , 1, X1*Y1%n]
		
		print u, p1, p_extended, d, ((X1)**2 +(Y1)**2 -1-d*(X1*Y1)**2)%n
		#return
		if(d==0 or d==1):
			continue
		p2 = p_extended[:]
		
		for pointer in range(10):
			p2 = Edwards_add_extended(p_extended, p2, 1, n)
			print pointer, p2, ( p2[0]*p2[0] + p2[1]*p2[1] - p2[2]*p2[2] - d*p2[3]*p2[3] )%n
			f = gcd(p2[2],n)
			if f!=1 and f!=n:
				print f

	print time.time() - start
		
#debug()

def prime_generator(n,lower_bound):
	'''print n primes over the lower_bound'''
	p = lower_bound
	for i in range(n):
		p = next_prime(p)
	return p
		
def semiprime_generator(d):
	'''Generate a 2d-digit semiprime n=ab, with a, b two d-digit primes'''
	a = 0
	b = 0
	for x in range(d-1):
		a += (random.randrange(10))*10**x
		b += (random.randrange(10))*10**x
	a += (1+random.randrange(9))*10**(d-1)
	b += (1+random.randrange(9))*10**(d-1)
	a = prime_generator(1,a)
	b = prime_generator(1,b)
	n = a*b
	return n
		
def testmode(lower_bound, higher_bound, rounds):
	for d in xrange(lower_bound, higher_bound):
		d_start = time.time()
		for r in range(rounds):
			start = time.time()
			n = long(semiprime_generator(d))
			print 
			print 'Factoring semiprime', r+1
			for factor in eecm(n):
				if(COLORED):
					print  colored(factor,'blue')
				else:
					print factor	
			print time.time() - start
		print 'average time for', d, 'digits prime:',(time.time() - d_start)/rounds
	
#testmode(10,26,100)


'''
History:
Version 0.1 2012-04-10 to 2012-04-20, 
			with projective coordinates only, 
			curve generation strategy: trivial
			
Version 0.2 2012-04-23 to 2012-04-28, 
			specialized in non-torsion points on Z/12Z with 'goodcurves'

Version 0.3 2012-04-29 to 2012-05-06,
			non-torsion points on Z/12Z generated from y^2=x^3-12x with p_weierstrass=(4,4)

Version 0.4 2012-04-30 to 2012-05-08,
			with completed(normal) coordinates (X:Z):(Y:T)

Version 0.5 2012-05-08 to 2012-05-15, the first version which works in the 'right' way!
			Z/2ZxZ/8Z construction (Theorem 7.2, 7.3 in [1])

Version 0.6 2012-05-10 to 2012-05-15,
			Z/12Z construction (Theorem 7.7, 7.8 in [1])
			
Version 1.0 2012-05-15 to ?
			Modifying BOUND stradegies

Reference:
[1] ECM using Edwards curves, http://eecm.cr.yp.to/index.html

'''
