// JavaOpt: -Xms10g -Xmx10g
// JaveVer: 11

import java.io.*;
import java.nio.MappedByteBuffer;
import java.nio.channels.FileChannel;
import java.nio.charset.StandardCharsets;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.BitSet;
import java.util.List;
import java.util.concurrent.*;
import java.util.concurrent.atomic.AtomicIntegerArray;
import java.util.concurrent.atomic.AtomicLongArray;
import java.util.concurrent.atomic.AtomicReferenceArray;

public class UrlFilterOk {

    static final byte PassPerm = '+';
    static final byte HitPerm = '-';
    static final byte InRange = '*';
    static final byte EqRange = '=';
    static final byte ExRange = '+';
    static final byte ThreadNum = 8;
    static final String EOF = "eof";
    static final String HTTP_DOT = "http:";
    static final String HTTPS_DOT = "https:";
    static final String HTTP_PORT = ":80";
    static final String HTTPS_PORT = ":443";
    static final String URL_PREFIX = "://";
    static final String URL_PRO = "//";
    static final byte[] HTTP_PORT_BYTES = reverse(HTTP_PORT.getBytes(StandardCharsets.US_ASCII));
    static final byte[] HTTP_PORTS_BYTES = reverse(HTTPS_PORT.getBytes(StandardCharsets.US_ASCII));

    static final int MODE_S = 2;
    static final int MODE_H = 1;
    static final int MODE_R = 0;

    static int inputType = -1;

    static final int VALUE_FLUSH_COUNT = 50000;
    static final double FALSE_POSITIVE_RATE = 0.001;

    static final int AVERAGE_DOMAIN_RULE_LENGTH = 18;
    static final int AVERAGE_PREFIX_RULE_LENGTH = 48;

    static BlockingQueue<String>[] printQueues = new BlockingQueue[ThreadNum];

    static BufferedWriter output = new BufferedWriter(new OutputStreamWriter(new
            FileOutputStream(FileDescriptor.out), StandardCharsets.US_ASCII), 512 * 1024);

    static int[] count_of_allowed = new int[]{0, 0, 0, 0, 0, 0, 0, 0};
    static int[] count_of_disallowed = new int[]{0, 0, 0, 0, 0, 0, 0, 0};
    static int[] count_of_no_hit = new int[]{0, 0, 0, 0, 0, 0, 0, 0};
    static long[] xor_of_allowed_value = new long[]{0, 0, 0, 0, 0, 0, 0, 0};
    static long[] xor_of_disallowed_value = new long[]{0, 0, 0, 0, 0, 0, 0, 0};

    static public class AttUrl {
        int domainUrlStart;
        int domainUrlStop;
        int pathOffset;
        byte[] portBytes = new byte[0];
        byte[] fullUrlBytes;

        public AttUrl(String fullUrl) {

            int p1, p2, p3;
            this.fullUrlBytes = fullUrl.getBytes(StandardCharsets.US_ASCII);

            p1 = fullUrl.indexOf(URL_PREFIX);
            p2 = fullUrl.indexOf(':', p1 + 3);
            p3 = fullUrl.indexOf('/', p1 + 3);

            this.pathOffset = p3;

            domainUrlStart = p1 + 3;
            if (p2 != -1 && p2 < p3) {
                domainUrlStop = p2;
            } else {
                domainUrlStop = p3;
                if (fullUrlBytes[4] == 's')
                    portBytes = HTTP_PORTS_BYTES;
                else
                    portBytes = HTTP_PORT_BYTES;
            }
        }

        public static AttUrl create(String url) {
            return new AttUrl(url);
        }
    }

    // Domain Postfix Filter
    static class DomainFilter {
        HashSet pass;
        HashSet passPort;
        HashSet hit;
        HashSet hitPort;

        ThreadLocal<byte[]> lastDomainHash = ThreadLocal.withInitial(() -> new byte[0]);
        ThreadLocal<Integer> lastDomainStart = ThreadLocal.withInitial(() -> 0);
        ThreadLocal<Integer> lastDomainStop = ThreadLocal.withInitial(() -> 0);
        ThreadLocal<List<Long>> localHashes = ThreadLocal.withInitial(() -> new ArrayList<>());
        ThreadLocal<Byte> lastDomainHashPerm = new ThreadLocal<>();

        BloomFilter bloomFilter;

        public void add(String postfix, char perm, Murmur3F mur) {
            var bytes = postfix.getBytes(StandardCharsets.US_ASCII);
            long hash = getUrlHash64Long(mur, reverse(bytes));
            bloomFilter.put(hash);
            int i = postfix.indexOf(':');
            if (perm == PassPerm) {
                if (i == -1) {
                    pass.add(hash);
                } else {
                    passPort.add(hash);
                }
            } else if (perm == HitPerm) {
                if (i == -1) {
                    hit.add(hash);
                } else {
                    hitPort.add(hash);
                }
            }
        }

        public ByteBufferFileMapper load(String file) throws IOException {

            File f = new File(file);
            int approximate = (int) (f.length() / AVERAGE_DOMAIN_RULE_LENGTH);
            bloomFilter = new BloomFilter(approximate, FALSE_POSITIVE_RATE);

            int hitSize = approximate;
            int passSize = approximate / 100;

            pass = new HashSet(passSize);
            passPort = new HashSet(passSize / 100);
            hit = new HashSet(hitSize);
            hitPort = new HashSet(hitSize / 100);

            return new ByteBufferFileMapper(file, 512 << 10);
        }

        public byte filter(AttUrl uri, Murmur3F mur) {

            if (inputType > MODE_R) {

                var preDomainBytes = lastDomainHash.get();
                int preDomainStart = lastDomainStart.get();
                int preDomainStop = lastDomainStop.get();

                if (Arrays.equals(preDomainBytes, preDomainStart, preDomainStop, uri.fullUrlBytes, uri.domainUrlStart, uri.pathOffset))
                    return lastDomainHashPerm.get();
            }

            mur.reset();

            List<Long> hashes = localHashes.get();
            hashes.clear();

            byte[] key = uri.fullUrlBytes;
            int offset = uri.domainUrlStart;
            int end = uri.pathOffset - 1;

            if (uri.portBytes.length > 0)
                mur.put(uri.portBytes);

            while (end >= offset) {
                byte cur = key[end];
                mur.put(cur);
                if (cur == '.') {
                    hashes.add(mur.mirrorHash());
                }
                if (end > offset) {
                    if (key[end - 1] == '.') {
                        hashes.add(mur.mirrorHash());
                    }
                }
                end--;
            }
            hashes.add(mur.mirrorHash());

            for (int i = hashes.size() - 1; i >= 0; i--) {
                long hash = hashes.get(i);
                if (!bloomFilter.contain(hash)) {
                    continue;
                }
                if (hitPort.contains(hash)) {
                    savePreDomainResult(uri, HitPerm);
                    return HitPerm;
                }
                if (passPort.contains(hash)) {
                    savePreDomainResult(uri, PassPerm);
                    return PassPerm;
                }
            }

            mur.reset();
            hashes.clear();

            key = uri.fullUrlBytes;
            offset = uri.domainUrlStart;
            end = uri.domainUrlStop - 1;

            while (end >= offset) {
                byte cur = key[end];
                mur.put(cur);
                if (cur == '.') {
                    hashes.add(mur.mirrorHash());
                }
                if (end > offset) {
                    byte pre = key[end - 1];
                    if (pre == '.') {
                        hashes.add(mur.mirrorHash());
                    }
                }
                end--;
            }
            hashes.add(mur.mirrorHash());

            for (int i = hashes.size() - 1; i >= 0; i--) {
                long hash = hashes.get(i);
                if (!bloomFilter.contain(hash)) {
                    continue;
                }
                if (hit.contains(hash)) {
                    savePreDomainResult(uri, HitPerm);
                    return HitPerm;
                }
                if (pass.contains(hash)) {
                    savePreDomainResult(uri, PassPerm);
                    return PassPerm;
                }
            }

            savePreDomainResult(uri, (byte) 0);

            return 0;
        }

        private void savePreDomainResult(AttUrl uri, byte passPerm) {
            lastDomainHash.set(uri.fullUrlBytes);
            lastDomainStart.set(uri.domainUrlStart);
            lastDomainStop.set(uri.pathOffset);
            lastDomainHashPerm.set(passPerm);
        }
    }

    static class UrlPrefixFilter {
        HashSet inPass;
        HashSet inPassRoot;
        HashSet inHit;
        HashSet inHitRoot;
        HashSet exPass;
        HashSet exPassRoot;
        HashSet exHit;
        HashSet exHitRoot;
        HashSet eqPass;
        HashSet eqHit;
        HashSet prefixUnRoots;
        BitSet[] prefixLengths = new BitSet[8192];

        BloomFilter eqFilter;
        BloomFilter preFilter;

        public void add(String prefix, char range, char perm, Murmur3F mur) {

            byte[] prefixBytes = prefix.getBytes(StandardCharsets.US_ASCII);
            if (range == EqRange && perm == PassPerm) {
                long prefixHash = getUrlHash64Long(mur, prefixBytes);
                eqPass.add(prefixHash);
                eqFilter.put(prefixHash);
            } else if (range == EqRange && perm == HitPerm) {
                long prefixHash = getUrlHash64Long(mur, prefixBytes);
                eqHit.add(prefixHash);
                eqFilter.put(prefixHash);
            } else {
                int rootPrefixPos = getRootPrefixPos(prefix);
                boolean rootPrefix = rootPrefixPos == prefix.length();
                mur.put(prefixBytes, 0, rootPrefixPos);
                long rootHash = mur.mirrorHash();
                mur.put(prefixBytes, rootPrefixPos, prefixBytes.length - rootPrefixPos);
                long prefixHash = mur.mirrorHash();
                mur.reset();
                preFilter.put(prefixHash);
                setLength(rootHash, prefix.length());

                if (range == InRange && perm == PassPerm) {
                    if (rootPrefix) {
                        inPassRoot.add(prefixHash);
                    } else {
                        inPass.add(prefixHash);
                        prefixUnRoots.add(rootHash);
                    }

                } else if (range == InRange && perm == HitPerm) {
                    if (rootPrefix) {
                        inHitRoot.add(prefixHash);
                    } else {
                        inHit.add(prefixHash);
                        prefixUnRoots.add(rootHash);
                    }
                } else if (range == ExRange && perm == PassPerm) {
                    if (rootPrefix) {
                        exPassRoot.add(prefixHash);
                    } else {
                        exPass.add(prefixHash);
                        prefixUnRoots.add(rootHash);
                    }
                } else if (range == ExRange && perm == HitPerm) {
                    if (rootPrefix) {
                        exHitRoot.add(prefixHash);
                    } else {
                        exHit.add(prefixHash);
                        prefixUnRoots.add(rootHash);
                    }
                }
            }
        }

        private int getRootPrefixPos(String prefix) {
            int p1 = prefix.indexOf(URL_PREFIX);
            int p2 = prefix.indexOf('/', p1 + 3);
            return p2 + 1;
        }

        void setLength(long domainHash, int offset) {
            int index = Long.hashCode(domainHash) & (8192 - 1);
            if (prefixLengths[index] == null) {
                synchronized (prefixLengths) {
                    if (prefixLengths[index] == null) {
                        prefixLengths[index] = new BitSet(3000);
                    }
                }
            }
            prefixLengths[index].set(offset);
        }

        public ByteBufferFileMapper load(String file) throws IOException {

            File f = new File(file);
            int approximate = (int) (f.length() / AVERAGE_PREFIX_RULE_LENGTH);
            int prefix = approximate / 3;
            int equal = prefix * 2;

            eqFilter = new BloomFilter(equal, FALSE_POSITIVE_RATE);
            preFilter = new BloomFilter(prefix, FALSE_POSITIVE_RATE);

            int hitEqSize = equal;
            int passEqSize = equal / 100;

            int hitPreSize = prefix;
            int passPreSize = prefix / 100;

            int hitPreSingleTypeSize = hitPreSize / 2;
            int passPreSingleTypeSize = passPreSize / 2;

            inPass = new HashSet(passPreSingleTypeSize / 3);
            inPassRoot = new HashSet(passPreSingleTypeSize);
            inHit = new HashSet(hitPreSingleTypeSize / 3);
            inHitRoot = new HashSet(hitPreSingleTypeSize);
            exPass = new HashSet(passPreSingleTypeSize / 3);
            exPassRoot = new HashSet(passPreSingleTypeSize);
            exHit = new HashSet(hitPreSingleTypeSize / 3);
            exHitRoot = new HashSet(hitPreSingleTypeSize);
            eqPass = new HashSet(passEqSize);
            eqHit = new HashSet(hitEqSize);
            prefixUnRoots = new HashSet(hitPreSize / 3);

            return new ByteBufferFileMapper(file, 512 << 10);
        }

        public byte filter(AttUrl uri, Murmur3F mur) {
            mur.reset();

            long urlHash = getUrlHash64Long(mur, uri.fullUrlBytes);
            if (eqFilter.contain(urlHash)) {
                if (eqHit.contains(urlHash))
                    return HitPerm;
                if (eqPass.contains(urlHash))
                    return PassPerm;
            }

            if (preFilter.contain(urlHash)) {
                if (inHit.contains(urlHash))
                    return HitPerm;
                if (inPass.contains(urlHash))
                    return PassPerm;
                if (inHitRoot.contains(urlHash))
                    return HitPerm;
                if (inPassRoot.contains(urlHash))
                    return PassPerm;
            }

            int rootPrefixPos = uri.pathOffset + 1;
            if (uri.fullUrlBytes.length == rootPrefixPos) {
                return 0;
            }

            urlHash = getUrlHash64Long(mur, uri.fullUrlBytes, 0, rootPrefixPos);

            if (!prefixUnRoots.contains(urlHash)) {

                if (preFilter.contain(urlHash)) {
                    if (exHitRoot.contains(urlHash)) {
                        return HitPerm;
                    }
                    if (exPassRoot.contains(urlHash)) {
                        return PassPerm;
                    }
                    if (inHitRoot.contains(urlHash)) {
                        return HitPerm;
                    }
                    if (inPassRoot.contains(urlHash)) {
                        return PassPerm;
                    }
                }
            } else {
                int find = uri.fullUrlBytes.length - 1;
                int stop = uri.pathOffset + 1;
                int index = Long.hashCode(urlHash) & (8192 - 1);
                while ((find = prefixLengths[index].previousSetBit(find)) > stop) {
                    urlHash = getUrlHash64Long(mur, uri.fullUrlBytes, 0, find--);
                    if (!preFilter.contain(urlHash)) {
                        continue;
                    }
                    if (exHit.contains(urlHash)) {
                        return HitPerm;
                    }
                    if (exPass.contains(urlHash)) {
                        return PassPerm;
                    }
                    if (inHit.contains(urlHash)) {
                        return HitPerm;
                    }
                    if (inPass.contains(urlHash)) {
                        return PassPerm;
                    }
                }

                if (find != -1) {

                    urlHash = getUrlHash64Long(mur, uri.fullUrlBytes, 0, find);

                    if (preFilter.contain(urlHash)) {
                        if (exHitRoot.contains(urlHash)) {
                            return HitPerm;
                        }
                        if (exPassRoot.contains(urlHash)) {
                            return PassPerm;
                        }
                        if (inHitRoot.contains(urlHash)) {
                            return HitPerm;
                        }
                        if (inPassRoot.contains(urlHash)) {
                            return PassPerm;
                        }
                    }
                }
            }

            return 0;
        }
    }

    static long getUrlHash64Long(Murmur3F mur, byte[] data) {
        long r = mur.hash(data);
        mur.reset();
        return r;
    }

    static long getUrlHash64Long(Murmur3F mur, byte[] data, int from, int to) {
        long r = mur.hash(data, from, to - from);
        mur.reset();
        return r;
    }

    public static byte[] reverse(byte[] array) {
        if (array == null) {
            return new byte[0];
        }
        int i = 0;
        int j = array.length - 1;
        byte tmp;
        while (j > i) {
            tmp = array[j];
            array[j] = array[i];
            array[i] = tmp;
            j--;
            i++;
        }
        return array;
    }

    public static void main(String[] args) throws IOException {

//        try {
//            Thread.sleep(15 * 1000);
//        } catch (InterruptedException e) {
//            e.printStackTrace();
//        }

        var inputTypeArg = args[3];
        switch (inputTypeArg) {
            case "R":
                inputType = MODE_R;
                break;
            case "H":
                inputType = MODE_H;
                break;
            case "S":
                inputType = MODE_S;
                break;
            default:
                inputType = MODE_R;
        }

        long startTime = System.currentTimeMillis();
        System.err.println(startTime);

        var domainFilter = new DomainFilter();
        var urlPrefixFilter = new UrlPrefixFilter();

        CountDownLatch latch = new CountDownLatch(ThreadNum);
        ExecutorService executor = Executors.newCachedThreadPool();

        //mmap
        var domainLoader = domainFilter.load(args[0]);

        var prefixLoader = urlPrefixFilter.load(args[1]);

        for (int c = 0; c < ThreadNum; c++) {
            executor.submit(() -> {
                try {
                    loadDomain(domainFilter, domainLoader);
                    loadPrefix(urlPrefixFilter, prefixLoader);
                } catch (IOException e) {
                    e.printStackTrace();
                } finally {
                    latch.countDown();
                }
            });
        }

        try {
            latch.await();
        } catch (InterruptedException e) {
            e.printStackTrace();
        }

        HashSet[] hashSets = new HashSet[]{
                domainFilter.hit, domainFilter.pass, domainFilter.hitPort, domainFilter.passPort,
                urlPrefixFilter.eqHit, urlPrefixFilter.eqPass,
                urlPrefixFilter.exHit, urlPrefixFilter.exPass, urlPrefixFilter.exHitRoot, urlPrefixFilter.exPassRoot,
                urlPrefixFilter.inHit, urlPrefixFilter.inPass, urlPrefixFilter.inHitRoot, urlPrefixFilter.inPassRoot,
                urlPrefixFilter.prefixUnRoots
        };

        CountDownLatch latchSort = new CountDownLatch(hashSets.length);

        for (int c = 0; c < hashSets.length; c++) {
            int index = c;
            executor.submit(() -> {
                try {
                    hashSets[index].sort();
                } catch (Exception e) {
                    e.printStackTrace();
                } finally {
                    latchSort.countDown();
                }
            });
        }

        try {
            latchSort.await();
        } catch (InterruptedException e) {
            e.printStackTrace();
        }

        for (int i = 0; i < printQueues.length; i++) {
            printQueues[i] = new ArrayBlockingQueue<>(1000);
        }

        var urlMapper = new ByteBufferFileMapper(args[2], 512 << 10);

        for (int c = 0; c < ThreadNum; c++) {
            int queueIndex = c;
            executor.submit(() -> {
                try {
                    UrlFilter(domainFilter, urlPrefixFilter, urlMapper, queueIndex);
                } catch (InterruptedException | IOException e) {
                    e.printStackTrace();
                }
            });
        }

        for (int c = 0; c < ThreadNum; c++) {
            int queueIndex = c;
            executor.submit(() -> {
                try {
                    String strValues;
                    var printQueue = printQueues[queueIndex];
                    while (!(strValues = printQueue.take()).equals(EOF)) {
                        output.write(strValues);
                        output.flush();
                    }
                } catch (InterruptedException | IOException e) {
                    e.printStackTrace();
                }
            });
        }

        executor.shutdown();
        try {
            executor.awaitTermination(Long.MAX_VALUE, TimeUnit.NANOSECONDS);
        } catch (InterruptedException e) {
            e.printStackTrace();
        }

        int total_count_of_allowed = 0;
        int total_count_of_disallowed = 0;
        int total_count_of_nohit = 0;
        long total_xor_of_allowed_value = 0;
        long total_xor_of_disallowed_value = 0;

        for (int i = 0; i < count_of_allowed.length; i++) {
            total_count_of_allowed += count_of_allowed[i];
        }

        for (int i = 0; i < count_of_disallowed.length; i++) {
            total_count_of_disallowed += count_of_disallowed[i];
        }

        for (int i = 0; i < count_of_no_hit.length; i++) {
            total_count_of_nohit += count_of_no_hit[i];
        }

        for (int i = 0; i < xor_of_allowed_value.length; i++) {
            total_xor_of_allowed_value ^= xor_of_allowed_value[i];
        }

        for (int i = 0; i < xor_of_disallowed_value.length; i++) {
            total_xor_of_disallowed_value ^= xor_of_disallowed_value[i];
        }

        System.out.println(total_count_of_allowed);
        System.out.println(total_count_of_disallowed);
        System.out.println(total_count_of_nohit);
        System.out.format("%08x\n", total_xor_of_allowed_value);
        System.out.format("%08x\n", total_xor_of_disallowed_value);

        long endTime = System.currentTimeMillis();
        System.err.println(endTime);

        System.err.println((endTime - startTime) / 1000F);
    }

    private static void UrlFilter(DomainFilter domainFilter, UrlPrefixFilter urlPrefixFilter, ByteBufferFileMapper mapper, int queueIndex) throws InterruptedException, IOException {

        String _url;
        int unFlushCount = 0;
        var printQueue = printQueues[queueIndex];
        Murmur3F mur = new Murmur3F();
        StringBuilder buffer = new StringBuilder(500000);
        MappedBufferReader reader;

        while ((reader = mapper.getReader()) != null) {
            while ((_url = reader.readLine()) != null) {

                int i = _url.indexOf('\t');
                String url = _url.substring(0, i);

                AttUrl u = AttUrl.create(url);
                byte retcode = domainFilter.filter(u, mur);
                if (retcode != HitPerm) {
                    byte oldretcode = retcode;
                    retcode = urlPrefixFilter.filter(u, mur);
                    if (retcode == 0) {
                        retcode = oldretcode;
                    }
                    if (retcode == 0) {
                        count_of_no_hit[queueIndex]++;
                        retcode = PassPerm;
                    }
                }
                if (retcode == PassPerm) {
                    var strValue = _url.substring(i + 1, i + 9);
                    var intValue = Long.parseLong(strValue, 16);
                    count_of_allowed[queueIndex]++;
                    xor_of_allowed_value[queueIndex] ^= intValue;
                    buffer.append(strValue);
                    buffer.append(System.lineSeparator());
                    unFlushCount++;
                    if (unFlushCount > VALUE_FLUSH_COUNT) {
                        printQueue.put(buffer.toString());
                        buffer.setLength(0);
                        buffer = new StringBuilder(500000);
                        unFlushCount = 0;
                    }
                } else if (retcode == HitPerm) {
                    var strValue = _url.substring(i + 1, i + 9);
                    var intValue = Long.parseLong(strValue, 16);
                    count_of_disallowed[queueIndex]++;
                    xor_of_disallowed_value[queueIndex] ^= intValue;
                }
            }
        }
        if (unFlushCount > 0) {
            printQueue.put(buffer.toString());
            buffer.setLength(0);
        }
        printQueue.put(EOF);
    }

    static void loadDomain(DomainFilter domainFilter, ByteBufferFileMapper mapper) throws IOException {

        MappedBufferReader reader;
        Murmur3F mur = new Murmur3F();
        while ((reader = mapper.getReader()) != null) {
            String _url;
            while ((_url = reader.readLine()) != null) {
                var i = _url.indexOf('\t');
                String postfix = _url.substring(0, i);
                char perm = _url.charAt(i + 1);
                domainFilter.add(postfix, perm, mur);
            }
        }
    }

    static void loadPrefix(UrlPrefixFilter urlPrefixFilter, ByteBufferFileMapper mapper) throws IOException {

        MappedBufferReader reader;
        Murmur3F mur = new Murmur3F();
        while ((reader = mapper.getReader()) != null) {
            String _url;
            while ((_url = reader.readLine()) != null) {
                var i = _url.indexOf('\t');
                var j = _url.indexOf('\t', i + 1);

                String prefix = _url.substring(0, i);
                char range = _url.charAt(i + 1);
                char perm = _url.charAt(j + 1);

                if (prefix.startsWith(URL_PRO)) {
                    String prefix1 = HTTP_DOT + prefix;
                    String prefix2 = HTTPS_DOT + prefix;
                    urlPrefixFilter.add(prefix1, range, perm, mur);
                    urlPrefixFilter.add(prefix2, range, perm, mur);
                } else {
                    urlPrefixFilter.add(prefix, range, perm, mur);
                }
            }
        }
    }

    static class HashSet {

        private static final int BUCKET_SIZE = 35;

        private static final float BUCKET_RESIZE_BY = 1.0f;

        private static final float LOAD_FACTOR = 0.75f;

        private static final int MAXIMUM_CAPACITY = 1 << 30;

        private int numOfArrays;

        private AtomicReferenceArray<long[]> hashTable;

        private AtomicIntegerArray writePoses;

        public HashSet(int num) {
            int size = num / BUCKET_SIZE + 1;
            int initialCapacity = size + Math.round((1 - LOAD_FACTOR) * size);
            this.numOfArrays = tableSizeFor(initialCapacity);

            hashTable = new AtomicReferenceArray<>(numOfArrays);
            writePoses = new AtomicIntegerArray(numOfArrays);
        }

        static int tableSizeFor(int cap) {
            int n = -1 >>> Integer.numberOfLeadingZeros(cap - 1);
            return (n < 0) ? 1 : (n >= MAXIMUM_CAPACITY) ? MAXIMUM_CAPACITY : n + 1;
        }

        public void add(long val) {
            int index = Long.hashCode(val) & (numOfArrays - 1);

            if (hashTable.get(index) == null) {
                hashTable.compareAndExchange(index, null, new long[BUCKET_SIZE]);
            }

            var indexesBucket = hashTable.get(index);
            int writePos = writePoses.getAndIncrement(index);
            if (writePos > indexesBucket.length - 1) {
                int addLength = Math.round(indexesBucket.length * BUCKET_RESIZE_BY);
                var newIndexesBucket = resizeBucket(indexesBucket, addLength);
                hashTable.compareAndExchange(index, indexesBucket, newIndexesBucket);
            }

            indexesBucket = hashTable.get(index);
            indexesBucket[writePos] = val;
        }

        public boolean contains(long val) {
            return find(val) >= 0;
        }

        public int find(long val) {
            int index = Long.hashCode(val) & (numOfArrays - 1);
            long[] bucket = hashTable.get(index);
            if (bucket == null) {
                return -1;
            }
            if (bucket.length <= 10) {
                return directSearch(bucket, val);
            }
            return Arrays.binarySearch(bucket, val);
        }

        public void sort() {
            for (int i = 0; i < numOfArrays; i++) {
                int writePos = writePoses.get(i);
                if (writePos == 0) {
                    continue;
                }

                long[] bucket = hashTable.get(i);
                if (writePos != bucket.length) {
                    int subLength = writePos - bucket.length;
                    hashTable.set(i, resizeBucket(bucket, subLength));
                }

                bucket = hashTable.get(i);
                if (bucket.length > 10) {
                    Arrays.parallelSort(bucket);
                }
            }
        }

        private int directSearch(long[] array, long v) {
            for (int i = 0; i < array.length; i++) {
                if (array[i] == v) {
                    return i;
                }
            }
            return -1;
        }

        private long[] resizeBucket(long[] bucket, int sizeDifference) {
            int length = bucket.length;
            int newLength = length + sizeDifference;
            long[] resizedBucket = new long[newLength];
            System.arraycopy(bucket, 0, resizedBucket, 0, sizeDifference < 0 ? newLength : length);
            return resizedBucket;
        }
    }

    public static class BloomFilter {

        private static final int LONG_ADDRESSABLE_BITS = 6;
        public final AtomicLongArray bits;
        private final int size;
        private final int numHashFunctions;

        public BloomFilter(int n, double falsePRate) {
            long bitSize = needBits(n, falsePRate);
            int numHashFunctions = needNumOfFunction(bitSize, n);
            size = (int) (bitSize >>> LONG_ADDRESSABLE_BITS) + 1;
            bits = new AtomicLongArray(size);
            this.numHashFunctions = numHashFunctions;
        }

        public boolean put(long hash) {
            long bitSize = size << LONG_ADDRESSABLE_BITS;
            int hash1 = (int) hash;
            int hash2 = (int) (hash >>> 32);
            boolean bitsChanged = false;
            for (int i = 1; i <= numHashFunctions; i++) {
                int combinedHash = hash1 + (i * hash2);
                if (combinedHash < 0) {
                    combinedHash = ~combinedHash;
                }
                bitsChanged |= set(combinedHash % bitSize);
            }
            return bitsChanged;
        }

        public boolean contain(long hash) {
            long bitSize = size << LONG_ADDRESSABLE_BITS;
            int hash1 = (int) hash;
            int hash2 = (int) (hash >>> 32);
            for (int i = 1; i <= numHashFunctions; i++) {
                int combinedHash = hash1 + (i * hash2);
                if (combinedHash < 0) {
                    combinedHash = ~combinedHash;
                }
                if (!get(combinedHash % bitSize)) {
                    return false;
                }
            }
            return true;
        }

        boolean set(long bitIndex) {
            if (get(bitIndex)) {
                return false;
            }
            int longIndex = (int) (bitIndex >>> LONG_ADDRESSABLE_BITS);
            long mask = 1L << bitIndex;

            long oldValue, newValue;
            do {
                oldValue = bits.get(longIndex);
                newValue = oldValue | mask;
                if (oldValue == newValue) {
                    return false;
                }
            } while (!bits.compareAndSet(longIndex, oldValue, newValue));
            return true;
        }

        boolean get(long bitIndex) {
            return (bits.get((int) (bitIndex >>> LONG_ADDRESSABLE_BITS)) & (1L << bitIndex)) != 0;
        }

        public static long needBits(int n, double falsePRate) {
            return -(long) (n * Math.log(falsePRate) / Math.pow(Math.log(2), 2)) + (1L << LONG_ADDRESSABLE_BITS);
        }

        public static int needNumOfFunction(long m, int n) {
            if (n <= 0) {
                return 1;
            }
            int num = (int) (m / n * Math.log(2));
            return num > 1 ? num : num + 1;
        }
    }

    public static class Murmur3F {
        private static final int CHUNK_SIZE = 16;
        private static final int LONG_SIZE = 8;
        private static final long C1 = 0x87c37b91114253d5L;
        private static final long C2 = 0x4cf5ad432745937fL;
        private byte[] remain = new byte[CHUNK_SIZE];
        private int remainIndex;
        private long h1;
        private long h2;
        private int length;

        public long hash() {
            getHash();
            return h1;
        }

        public long[] hash(long[] work) {
            getHash();
            if (work == null) {
                work = new long[2];
            }
            work[0] = h1;
            work[1] = h2;
            return work;
        }

        public long hash(byte[] bs) {
            put(bs);
            return hash();
        }

        public long hash(byte[] bs, int from, int length) {
            put(bs, from, length);
            return hash();
        }

        public long[] hash(byte[] bs, long[] work) {
            put(bs);
            return hash(work);
        }

        private void getHash() {
            processRemaining();
            h1 ^= length;
            h2 ^= length;

            h1 += h2;
            h2 += h1;

            h1 = fmix64(h1);
            h2 = fmix64(h2);

            h1 += h2;
            h2 += h1;
        }

        public long mirrorHash() {
            long tmpH1 = h1;
            long tmpH2 = h2;
            int tmpLength = length;
            long hashCode = hash();
            h1 = tmpH1;
            h2 = tmpH2;
            length = tmpLength;
            return hashCode;
        }

        public long[] mirrorHash(long[] work) {
            long tmpH1 = h1;
            long tmpH2 = h2;
            int tmpLength = length;
            long[] hashCode = hash(work);
            h1 = tmpH1;
            h2 = tmpH2;
            length = tmpLength;
            return hashCode;
        }

        public long[] mirrorHash(byte[] bs, long[] work) {
            byte[] tmpRemain = null;
            if (remainIndex + bs.length > CHUNK_SIZE) { // remain array will be override
                tmpRemain = new byte[CHUNK_SIZE];
                System.arraycopy(remain, 0, tmpRemain, 0, CHUNK_SIZE);
            }
            int tmpRemainIndex = remainIndex;
            long tmpH1 = h1;
            long tmpH2 = h2;
            int tmpLength = length;
            put(bs);
            long[] hashCode = mirrorHash(work);
            if (tmpRemain != null) {
                remain = tmpRemain;
            }
            remainIndex = tmpRemainIndex;
            h1 = tmpH1;
            h2 = tmpH2;
            length = tmpLength;
            return hashCode;
        }

        public void put(byte b) {
            remain[remainIndex] = b;
            remainIndex++;
            if (remainIndex == CHUNK_SIZE) {
                process();
            }
        }

        public void put(long value) { // Little endian
            for (int i = 0; i < LONG_SIZE; i++) {
                put((byte) (value & 0xffL));
                value >>= 8;
            }
        }

        public void put(byte[] bs) {
            put(bs, 0, bs.length);
        }

        public void put(byte[] bs, int from, int length) {
            int bl = length;
            int to = from + length;
            if (bl < CHUNK_SIZE) {
                for (int i = from; i < to; i++) {
                    put(bs[i]);
                }
            } else {
                int cursor = from;
                if (remainIndex != 0) {
                    while (remainIndex != CHUNK_SIZE) {
                        remain[remainIndex] = bs[cursor];
                        remainIndex++;
                        cursor++;
                    }
                    process();
                }
                while ((to - cursor) >= CHUNK_SIZE) {
                    long k1 = Longs.fromBytes(bs[cursor], bs[cursor + 1], bs[cursor + 2], bs[cursor + 3],
                            bs[cursor + 4], bs[cursor + 5], bs[cursor + 6], bs[cursor + 7]);
                    cursor += 8;
                    long k2 = Longs.fromBytes(bs[cursor], bs[cursor + 1], bs[cursor + 2], bs[cursor + 3],
                            bs[cursor + 4], bs[cursor + 5], bs[cursor + 6], bs[cursor + 7]);
                    cursor += 8;
                    process(k1, k2);
                }
                while (cursor < to) {
                    remain[remainIndex] = bs[cursor];
                    remainIndex++;
                    cursor++;
                }
            }
        }

        public void put(char c) {
            if (c <= 0x7F) {
                put((byte) c);
            } else {
                put(Character.toString(c).getBytes());
            }
        }

        public Murmur3F reset() {
            remainIndex = 0;
            h1 = 0;
            h2 = 0;
            length = 0;
            return this;
        }

        public void process() {
            long k1 = Longs.fromBytes(remain[0], remain[1], remain[2], remain[3], remain[4], remain[5], remain[6], remain[7]);
            long k2 = Longs.fromBytes(remain[8], remain[9], remain[10], remain[11], remain[12], remain[13], remain[14], remain[15]);
            process(k1, k2);
            remainIndex = 0;
        }

        private void process(long k1, long k2) {
            h1 ^= mixK1(k1);

            h1 = Long.rotateLeft(h1, 27);
            h1 += h2;
            h1 = h1 * 5 + 0x52dce729;

            h2 ^= mixK2(k2);

            h2 = Long.rotateLeft(h2, 31);
            h2 += h1;
            h2 = h2 * 5 + 0x38495ab5;

            length += CHUNK_SIZE;
        }

        private static long mixK1(long k1) {
            k1 *= C1;
            k1 = Long.rotateLeft(k1, 31);
            k1 *= C2;
            return k1;
        }

        private static long mixK2(long k2) {
            k2 *= C2;
            k2 = Long.rotateLeft(k2, 33);
            k2 *= C1;
            return k2;
        }

        private static long fmix64(long k) {
            k ^= k >>> 33;
            k *= 0xff51afd7ed558ccdL;
            k ^= k >>> 33;
            k *= 0xc4ceb9fe1a85ec53L;
            k ^= k >>> 33;
            return k;
        }

        private void processRemaining() {
            if (remainIndex == 0) return;
            long k1 = 0;
            long k2 = 0;
            length += remainIndex;
            switch (remainIndex) {
                case 15:
                    k2 ^= (long) toInt(remain[14]) << 48; // fall through
                case 14:
                    k2 ^= (long) toInt(remain[13]) << 40; // fall through
                case 13:
                    k2 ^= (long) toInt(remain[12]) << 32; // fall through
                case 12:
                    k2 ^= (long) toInt(remain[11]) << 24; // fall through
                case 11:
                    k2 ^= (long) toInt(remain[10]) << 16; // fall through
                case 10:
                    k2 ^= (long) toInt(remain[9]) << 8; // fall through
                case 9:
                    k2 ^= toInt(remain[8]); // fall through
                case 8:
                    k1 ^= Longs.fromBytes(remain[0], remain[1], remain[2], remain[3], remain[4], remain[5], remain[6], remain[7]);
                    break;
                case 7:
                    k1 ^= (long) toInt(remain[6]) << 48; // fall through
                case 6:
                    k1 ^= (long) toInt(remain[5]) << 40; // fall through
                case 5:
                    k1 ^= (long) toInt(remain[4]) << 32; // fall through
                case 4:
                    k1 ^= (long) toInt(remain[3]) << 24; // fall through
                case 3:
                    k1 ^= (long) toInt(remain[2]) << 16; // fall through
                case 2:
                    k1 ^= (long) toInt(remain[1]) << 8; // fall through
                case 1:
                    k1 ^= toInt(remain[0]);
                    break;
                default:
                    throw new AssertionError("Should never get here.");
            }
            h1 ^= mixK1(k1);
            h2 ^= mixK2(k2);
        }

        public static int toInt(byte value) {
            return value & 0xFF;
        }
    }

    public static class Longs {

        public static long fromBytes(byte b1, byte b2, byte b3, byte b4, byte b5, byte b6, byte b7, byte b8) {
            return fromBytesBigEndian(b8, b7, b6, b5, b4, b3, b2, b1);
        }

        public static long fromBytesBigEndian(byte b1, byte b2, byte b3, byte b4, byte b5, byte b6, byte b7, byte b8) {
            return (b1 & 0xFFL) << 56
                    | (b2 & 0xFFL) << 48
                    | (b3 & 0xFFL) << 40
                    | (b4 & 0xFFL) << 32
                    | (b5 & 0xFFL) << 24
                    | (b6 & 0xFFL) << 16
                    | (b7 & 0xFFL) << 8
                    | (b8 & 0xFFL);
        }
    }

    /**
     * read line, not decode
     */
    public static class MappedBufferReader {
        private static final int workLen = 40;
        private String remains;
        private MappedByteBuffer buffer;
        private char[] work;
        private boolean hasRemain;

        public MappedBufferReader(MappedByteBuffer buffer, String remains) {
            this.remains = remains;
            this.hasRemain = remains == null ? false : true;
            this.buffer = buffer;
            work = new char[workLen];
        }

        public void load() {
            buffer.load();
        }

        public String readLine() {
            for (int i = 0; i < workLen; i++) {
                if (buffer.hasRemaining()) {
                    int c = buffer.get();
                    if (c == '\n') {
                        return new String(work, 0, i);
                    } else {
                        work[i] = (char) c;
                    }
                } else {
                    String s = new String(work, 0, i);
                    if (hasRemain) {
                        hasRemain = false;
                        return s.length() + remains.length() > 0 ? s + remains : null;
                    } else {
                        return s.length() > 0 ? s : null;
                    }
                }
            }
            StringBuilder sb = new StringBuilder(new String(work));
            while (true) {
                if (buffer.hasRemaining()) {
                    int c = buffer.get();
                    if (c == '\n') {
                        return sb.toString();
                    } else {
                        sb.append((char) c);
                    }
                } else {
                    if (hasRemain) {
                        hasRemain = false;
                        sb.append(remains);
                    }
                    return sb.toString();
                }
            }
        }

        public static String readLine(MappedByteBuffer buffer, char[] work) {
            int len = work.length;
            for (int i = 0; i < len; i++) {
                int c;
                if (!buffer.hasRemaining() || (c = buffer.get()) == '\n') {
                    String s = new String(work, 0, i);
                    return s.length() > 0 ? s : null;
                }
                work[i] = (char) c;
            }
            // String longer than work
            StringBuilder sb = new StringBuilder(new String(work));
            int c;
            while (buffer.hasRemaining() && (c = buffer.get()) != '\n') {
                sb.append((char) c);
            }
            return sb.toString();
        }
    }

    public static class ByteBufferFileMapper {
        private FileChannel ic;
        private long bufferSize;
        private MappedByteBuffer buffer;
        private long fileSize;
        private int part;

        public ByteBufferFileMapper(String filePath, int bufferSize) throws IOException {
            this.bufferSize = bufferSize;
            File file = new File(filePath);
            fileSize = file.length();
            ic = new FileInputStream(file).getChannel();
            buffer = ic.map(FileChannel.MapMode.READ_ONLY, 0, nextSize());
            buffer.load();
            part = 1;
        }

        synchronized public MappedBufferReader getReader() throws IOException {
            // read over
            if (buffer == null) {
                return null;
            }
            // last buffer remain
            long nextSize = nextSize();
            if (nextSize <= 0) {
                MappedBufferReader reader = new MappedBufferReader(buffer, null);
                buffer = null;
                return reader;
            }
            // has bytes not mapped
            MappedByteBuffer nextBuffer = ic.map(FileChannel.MapMode.READ_ONLY, bufferSize * part, nextSize);
            nextBuffer.load();
            part++;
            String remains = MappedBufferReader.readLine(nextBuffer, new char[40]);
            MappedBufferReader reader = new MappedBufferReader(buffer, remains);
            buffer = nextBuffer;
            return reader;
        }

        private long nextSize() {
            long base = part * bufferSize;
            long remain = fileSize - base;
            return remain > bufferSize ? bufferSize : remain;
        }
    }
}