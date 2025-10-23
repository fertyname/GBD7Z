import java.math.BigInteger;
import java.nio.ByteBuffer;
import java.nio.charset.StandardCharsets;
import java.util.*;

public class GBD7Z {

 private static final String MAGIC = "GBD7Z:";
 private static final String TAIL = "&7";
 private static final int BLOCK_BYTES = 16;
 private static final long HASH_SEED = 0x9E3779B97F4A7C15L;
 private static final BigInteger MOD_2_128 = BigInteger.ONE.shiftLeft(128);
 private static final int ALPHABET_SIZE = 91;
 private static final char BASE0 = '!';

 public static String encrypt(byte[] key, byte[] plaintext) throws Exception {
     requireNonNull(key, "key");
     requireNonNull(plaintext, "plaintext");
     if (key.length == 0) throw new IllegalArgumentException("key must be non-empty");

     SplitResult split = split3WithCountsAndBase(plaintext);
     int[] chaos = logisticChaos(key, 256);
     byte[] streamed = streamFlowEncrypt(split.leaves, key, chaos);
     byte[] blocked = blockSyncEncrypt(streamed, key, chaos);
     byte[] payload = buildPayload(split.counts, split.bases, blocked);
     long h64 = rollingHash64(payload, key);
     String hashHex = String.format("%016x", h64);
     String encPayload = encodePayload(payload);
     return MAGIC + encPayload + "|" + hashHex + TAIL;
 }

 public static byte[] decrypt(byte[] key, String envelope) throws Exception {
     requireNonNull(key, "key");
     requireNonNull(envelope, "envelope");
     if (!envelope.startsWith(MAGIC) || !envelope.endsWith(TAIL))
         throw new IllegalArgumentException("Not a GBD7Z envelope");

     String inner = envelope.substring(MAGIC.length(), envelope.length() - TAIL.length());
     int sep = inner.lastIndexOf('|');
     if (sep <= 0) throw new IllegalArgumentException("Invalid envelope format");
     String encPayload = inner.substring(0, sep);
     String hashHex = inner.substring(sep + 1);
     if (hashHex.length() != 16) throw new IllegalArgumentException("Bad hash");
     byte[] payload = decodePayload(encPayload);
     long expectedHash = Long.parseUnsignedLong(hashHex, 16);
     long gotHash = rollingHash64(payload, key);
     if (gotHash != expectedHash) throw new SecurityException("hash mismatch — wrong key or corrupt data");
     PayloadParts parts = parsePayload(payload);
     int[] chaos = logisticChaos(key, 256);
     byte[] streamed = blockSyncDecrypt(parts.data, key, chaos);
     byte[] leaves = streamFlowDecrypt(streamed, key, chaos);
     byte[] original = inverseSplit3FromCountsAndBase(leaves, parts.counts, parts.bases);

     return original;
 }

 private static class SplitResult {
     final byte[] leaves;
     final int[] counts;
     final byte[] bases;
     SplitResult(byte[] leaves, int[] counts, byte[] bases) { this.leaves = leaves; this.counts = counts; this.bases = bases; }
 }

 private static SplitResult split3WithCountsAndBase(byte[] input) {
     List<Byte> leaves = new ArrayList<>();
     int[] counts = new int[input.length];
     byte[] bases = new byte[input.length];
     for (int i = 0; i < input.length; i++) {
         int v = input[i] & 0xFF;
         if (v == 0) {
             leaves.add((byte)0);
             counts[i] = 1;
             bases[i] = 0;
             continue;
         }
         int temp = v;
         int levels = 0;
         while (temp % 3 == 0 && temp > 0) {
             temp /= 3;
             levels++;
         }
         int leafCount = 1;
         for (int j = 0; j < levels; j++) leafCount *= 3;
         for (int j = 0; j < leafCount; j++) leaves.add((byte) temp);
         counts[i] = leafCount;
         bases[i] = (byte) temp;
         long reconstructed = (long) (temp & 0xFF) * (long) leafCount;
         if (reconstructed != v) {
         }
     }
     byte[] L = new byte[leaves.size()];
     for (int i = 0; i < L.length; i++) L[i] = leaves.get(i);
     return new SplitResult(L, counts, bases);
 }

 private static byte[] inverseSplit3FromCountsAndBase(byte[] leaves, int[] counts, byte[] bases) {
     int pos = 0;
     byte[] out = new byte[counts.length];
     for (int i = 0; i < counts.length; i++) {
         int c = counts[i];
         if (c <= 0) throw new IllegalArgumentException("invalid count");
         if (pos + c > leaves.length) throw new IllegalArgumentException("leaf array too short");
         int base = bases[i] & 0xFF;
         long original = (long) base * (long) c;
         if (original < 0 || original > 255) {
             throw new IllegalStateException("reconstructed byte out of range from base*count (base="
                     + base + ", count=" + c + ", product=" + original + ")");
         }
         out[i] = (byte) ((int) original & 0xFF);
         pos += c;
     }
     if (pos != leaves.length) throw new IllegalStateException("extra leaves present");
     return out;
 }
 private static int[] logisticChaos(byte[] key, int len) {
     long sum = 0;
     for (byte b : key) sum += (b & 0xFF);
     double x = (sum % 1024) / 1024.0 + 0.123456;
     double rBase = 3.9 + ((key[0] & 0xFF) % 9) * 0.01;
     int[] out = new int[len];
     for (int i = 0; i < len; i++) {
         x = (rBase * x * (1.0 - x)) % 1.0;
         int v = (int)Math.floor((x - Math.floor(x)) * 256.0) & 0xFF;
         out[i] = v;
         rBase += (((key[i % key.length] & 0xFF) % 5) - 2) * 0.0003;
     }
     return out;
 }

 private static byte[] streamFlowEncrypt(byte[] data, byte[] key, int[] chaos) {
     byte[] out = new byte[data.length];
     int prev = initIvByte(key);
     for (int i = 0; i < data.length; i++) {
         int k = key[i % key.length] & 0xFF;
         int ch = chaos[i % chaos.length] & 0xFF;
         int tmp = ( (data[i] & 0xFF) + k + ch ) & 0xFF;
         int shift = ((k ^ ch) & 7) + 1;
         int rot = rotr8(tmp, shift);
         int c = rot ^ prev;
         out[i] = (byte) (c & 0xFF);
         prev = c & 0xFF;
     }
     return out;
 }
 private static byte[] streamFlowDecrypt(byte[] cipher, byte[] key, int[] chaos) {
     byte[] out = new byte[cipher.length];
     int prev = initIvByte(key);
     for (int i = 0; i < cipher.length; i++) {
         int c = cipher[i] & 0xFF;
         int k = key[i % key.length] & 0xFF;
         int ch = chaos[i % chaos.length] & 0xFF;
         int rot = c ^ prev;
         int shift = ((k ^ ch) & 7) + 1;
         int tmp = rotl8(rot, shift);
         int val = (tmp - k - ch) & 0xFF;
         out[i] = (byte) val;
         prev = c;
     }
     return out;
 }

 private static int initIvByte(byte[] key) {
     int s = 0xA5;
     for (int i = 0; i < key.length; i++) s = (s * 31 + (key[i] & 0xFF)) & 0xFF;
     return s;
 }

 private static int rotr8(int v, int r) {
     r &= 7;
     return ((v >>> r) | ((v << (8 - r)) & 0xFF)) & 0xFF;
 }
 private static int rotl8(int v, int r) {
     r &= 7;
     return (( (v << r) | (v >>> (8 - r)) ) & 0xFF);
 }

 private static byte[] blockSyncEncrypt(byte[] data, byte[] key, int[] chaos) {
     if (data.length == 0) return new byte[0];
     int rounds = 7;
     BigInteger mul = deriveOddMultiplier(key, 0);
     ByteBuffer bb = ByteBuffer.allocate(((data.length + BLOCK_BYTES - 1) / BLOCK_BYTES) * BLOCK_BYTES);
     bb.put(Arrays.copyOf(data, ((data.length + BLOCK_BYTES - 1) / BLOCK_BYTES) * BLOCK_BYTES));
     byte[] buf = bb.array();
     for (int blockIdx = 0; blockIdx < buf.length; blockIdx += BLOCK_BYTES) {
         byte[] block = Arrays.copyOfRange(buf, blockIdx, blockIdx + BLOCK_BYTES);
         BigInteger N = new BigInteger(1, block);
         for (int r = 0; r < rounds; r++) {
             BigInteger k1 = derive128FromKey(key, r, 1);
             BigInteger k2 = derive128FromKey(key, r, 2);
             N = N.add(k1).mod(MOD_2_128);
             N = N.multiply(mul).mod(MOD_2_128);
             byte[] nb = toFixedLengthBytes(N, BLOCK_BYTES);
             permuteBytesInplace(nb, chaos, r);
             N = new BigInteger(1, nb);
             N = N.xor(k2);
         }
         byte[] encBlock = toFixedLengthBytes(N, BLOCK_BYTES);
         System.arraycopy(encBlock, 0, buf, blockIdx, BLOCK_BYTES);
     }
     return Arrays.copyOf(buf, data.length);
 }

 private static byte[] blockSyncDecrypt(byte[] data, byte[] key, int[] chaos) {
     if (data.length == 0) return new byte[0];
     int rounds = 7;
     BigInteger mul = deriveOddMultiplier(key, 0);
     BigInteger mulInv = mul.modInverse(MOD_2_128);
     ByteBuffer bb = ByteBuffer.allocate(((data.length + BLOCK_BYTES - 1) / BLOCK_BYTES) * BLOCK_BYTES);
     bb.put(Arrays.copyOf(data, ((data.length + BLOCK_BYTES - 1) / BLOCK_BYTES) * BLOCK_BYTES));
     byte[] buf = bb.array();
     for (int blockIdx = 0; blockIdx < buf.length; blockIdx += BLOCK_BYTES) {
         byte[] block = Arrays.copyOfRange(buf, blockIdx, blockIdx + BLOCK_BYTES);
         BigInteger N = new BigInteger(1, block);
         for (int r = rounds - 1; r >= 0; r--) {
             BigInteger k1 = derive128FromKey(key, r, 1);
             BigInteger k2 = derive128FromKey(key, r, 2);
             N = N.xor(k2);
             byte[] nb = toFixedLengthBytes(N, BLOCK_BYTES);
             inversePermuteBytesInplace(nb, chaos, r);
             N = new BigInteger(1, nb);
             N = N.multiply(mulInv).mod(MOD_2_128);
             N = N.subtract(k1).mod(MOD_2_128);
         }
         byte[] decBlock = toFixedLengthBytes(N, BLOCK_BYTES);
         System.arraycopy(decBlock, 0, buf, blockIdx, BLOCK_BYTES);
     }
     return Arrays.copyOf(buf, data.length);
 }

 private static BigInteger deriveOddMultiplier(byte[] key, int salt) {
     byte[] buf = new byte[16];
     for (int i = 0; i < 16; i++) buf[i] = key[(i + salt) % key.length];
     buf[15] = (byte) (buf[15] | 1);
     return new BigInteger(1, buf);
 }

 private static BigInteger derive128FromKey(byte[] key, int round, int which) {
     byte[] buf = new byte[16];
     for (int i = 0; i < 16; i++) {
         int v = key[(i + round + which) % key.length] & 0xFF;
         v = (v + ((round * 31) ^ (which * 13))) & 0xFF;
         buf[i] = (byte) v;
     }
     return new BigInteger(1, buf);
 }

 private static byte[] toFixedLengthBytes(BigInteger v, int len) {
     byte[] raw = v.toByteArray();
     if (raw.length == len) return raw;
     byte[] out = new byte[len];
     if (raw.length > len) {
         System.arraycopy(raw, raw.length - len, out, 0, len);
     } else {
         System.arraycopy(raw, 0, out, len - raw.length, raw.length);
     }
     return out;
 }

 private static void permuteBytesInplace(byte[] b, int[] chaos, int round) {
     int n = b.length;
     for (int i = 0; i < n; i++) {
         int j = (i + chaos[(i + round) % chaos.length]) % n;
         byte t = b[i]; b[i] = b[j]; b[j] = t;
     }
 }
 private static void inversePermuteBytesInplace(byte[] b, int[] chaos, int round) {
     int n = b.length;
     for (int i = n - 1; i >= 0; i--) {
         int j = (i + chaos[(i + round) % chaos.length]) % n;
         byte t = b[i]; b[i] = b[j]; b[j] = t;
     }
 }
 private static byte[] buildPayload(int[] counts, byte[] bases, byte[] data) {
     int origLen = counts.length;
     ByteBuffer bb = ByteBuffer.allocate(4 + 4 + origLen * 4 + origLen + data.length);
     bb.putInt(origLen);
     bb.putInt(origLen);
     for (int v : counts) bb.putInt(v);
     for (byte b : bases) bb.put(b);
     bb.put(data);
     return bb.array();
 }

 private static class PayloadParts {
     final int[] counts;
     final byte[] bases;
     final byte[] data;
     PayloadParts(int[] counts, byte[] bases, byte[] data) { this.counts = counts; this.bases = bases; this.data = data; }
 }

 private static PayloadParts parsePayload(byte[] payload) {
     ByteBuffer bb = ByteBuffer.wrap(payload);
     int origLen = bb.getInt();
     int countsLen = bb.getInt();
     if (countsLen != origLen) throw new IllegalArgumentException("payload counts length mismatch");
     int[] counts = new int[origLen];
     for (int i = 0; i < origLen; i++) counts[i] = bb.getInt();
     byte[] bases = new byte[origLen];
     bb.get(bases);
     byte[] data = new byte[bb.remaining()];
     bb.get(data);
     return new PayloadParts(counts, bases, data);
 }

 private static long rollingHash64(byte[] data, byte[] key) {
     long h = HASH_SEED;
     for (int i = 0; i < data.length; i++) {
         h = Long.rotateLeft(h ^ (data[i] & 0xFFL), 11) + mixKey64(key, i);
     }
     h = h ^ (h >>> 33);
     h = h * 0xff51afd7ed558ccdL;
     h = h ^ (h >>> 33);
     return h;
 }

 private static long mixKey64(byte[] key, int i) {
     long v = 0x9E3779B97F4A7C15L;
     for (int j = 0; j < key.length; j++) {
         v = Long.rotateLeft(v + (key[j] & 0xFFL) + i, (j & 63));
     }
     return v;
 }

 private static String encodePayload(byte[] data) {
     StringBuilder sb = new StringBuilder(data.length * 2);
     for (byte b : data) {
         int v = b & 0xFF;
         int hi = v / ALPHABET_SIZE;
         int lo = v % ALPHABET_SIZE;
         sb.append((char)(BASE0 + hi));
         sb.append((char)(BASE0 + lo));
     }
     return sb.toString();
 }
 private static byte[] decodePayload(String s) {
     if ((s.length() & 1) != 0) throw new IllegalArgumentException("payload length odd");
     byte[] out = new byte[s.length() / 2];
     for (int i = 0; i < out.length; i++) {
         int hi = s.charAt(2*i) - BASE0;
         int lo = s.charAt(2*i + 1) - BASE0;
         if (hi < 0 || hi >= ALPHABET_SIZE || lo < 0 || lo >= ALPHABET_SIZE)
             throw new IllegalArgumentException("invalid char in payload");
         int v = hi * ALPHABET_SIZE + lo;
         out[i] = (byte)(v & 0xFF);
     }
     return out;
 }

 private static void requireNonNull(Object o, String name) {
     if (o == null) throw new NullPointerException(name + " is null");
 }
 
 public static void main(String[] args) throws Exception {
	try (Scanner scanner = new Scanner(System.in)) {
		System.out.println("Сообщение для шифрования:");
		 String text = scanner.nextLine();
		 
		 System.out.println("Ключ для шифрования: ");
		 String key = scanner.nextLine();
		 test(text, key);
	}
 }

 private static void test(String plain, String keyStr) throws Exception {
     byte[] key = keyStr.getBytes(StandardCharsets.UTF_8);
     System.out.println("Plain : " + plain);
     String enc = encrypt(key, plain.getBytes(StandardCharsets.UTF_8));
     System.out.println("Encrypted : " + enc);
     byte[] dec = decrypt(key, enc);
     System.out.println("Decrypted : " + new String(dec, StandardCharsets.UTF_8));
     System.out.println("----");
 }
}
