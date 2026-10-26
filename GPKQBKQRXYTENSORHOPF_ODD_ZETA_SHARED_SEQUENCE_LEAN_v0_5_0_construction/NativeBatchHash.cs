// Offline Windows .NET Framework 4 helper. No Lean execution or build logic.
// Manifest: UTF-16LE with BOM, one absolute path per line.
// Result: ASCII, zero-based input index TAB lowercase SHA256, in input order.
// The result is published only after every input has been read successfully.
using System;
using System.Collections.Generic;
using System.Globalization;
using System.IO;
using System.Security.Cryptography;
using System.Text;
using System.Threading;

internal static class NativeBatchHash
{
    private const int FileBufferBytes = 131072;

    private sealed class Batch
    {
        internal readonly string[] Paths;
        internal readonly string[] Hashes;
        internal readonly object Gate = new object();
        internal int Next = -1;
        internal int Completed;
        internal volatile string Failure;

        internal Batch(string[] paths)
        {
            Paths = paths;
            Hashes = new string[paths.Length];
        }

        internal void Work()
        {
            try
            {
                using (SHA256 sha = SHA256.Create())
                {
                    if (sha == null) throw new InvalidOperationException("SHA256_UNAVAILABLE");
                    while (Failure == null)
                    {
                        int index = Interlocked.Increment(ref Next);
                        if (index >= Paths.Length) return;
                        sha.Initialize();
                        using (FileStream input = new FileStream(Paths[index], FileMode.Open,
                            FileAccess.Read, FileShare.Read, FileBufferBytes, FileOptions.SequentialScan))
                        {
                            long length = input.Length;
                            Hashes[index] = Hex(sha.ComputeHash(input));
                            if (input.Length != length || input.Position != length)
                                throw new IOException("INPUT_LENGTH_CHANGED=" + Paths[index]);
                        }
                        lock (Gate)
                        {
                            Completed++;
                            if (Completed % 200 == 0 || Completed == Paths.Length)
                            {
                                Console.WriteLine("HASH_PROGRESS=" + Completed.ToString(CultureInfo.InvariantCulture)
                                    + "/" + Paths.Length.ToString(CultureInfo.InvariantCulture));
                                Console.Out.Flush();
                            }
                        }
                    }
                }
            }
            catch (Exception error)
            {
                lock (Gate)
                {
                    if (Failure == null) Failure = ErrorText(error);
                }
            }
        }
    }

    private static string Hex(byte[] bytes)
    {
        const string digits = "0123456789abcdef";
        char[] result = new char[bytes.Length * 2];
        for (int i = 0; i < bytes.Length; i++)
        {
            result[2 * i] = digits[bytes[i] >> 4];
            result[2 * i + 1] = digits[bytes[i] & 15];
        }
        return new string(result);
    }

    private static string ErrorText(Exception error)
    {
        string message = error.GetType().Name + ":" + error.Message;
        message = message.Replace('\r', ' ').Replace('\n', ' ').Replace('\t', ' ');
        return message.Length <= 512 ? message : message.Substring(0, 512);
    }

    private static string AbsolutePath(string path)
    {
        if (String.IsNullOrEmpty(path) || path.IndexOfAny(new char[] { '\r', '\n', '\t', '\0' }) >= 0)
            throw new ArgumentException("INVALID_PATH_TEXT");
        bool drive = path.Length >= 3 && ((path[0] >= 'A' && path[0] <= 'Z')
            || (path[0] >= 'a' && path[0] <= 'z')) && path[1] == ':'
            && (path[2] == '\\' || path[2] == '/');
        bool unc = path.StartsWith("\\\\", StringComparison.Ordinal)
            && !path.StartsWith("\\\\?\\", StringComparison.Ordinal)
            && !path.StartsWith("\\\\.\\", StringComparison.Ordinal);
        if (!drive && !unc) throw new ArgumentException("ABSOLUTE_WINDOWS_PATH_REQUIRED");
        return Path.GetFullPath(path);
    }

    private static string[] ReadManifest(string manifest, string output)
    {
        List<string> paths = new List<string>();
        HashSet<string> seen = new HashSet<string>(StringComparer.OrdinalIgnoreCase);
        using (FileStream input = new FileStream(manifest, FileMode.Open, FileAccess.Read, FileShare.Read))
        {
            if (input.ReadByte() != 255 || input.ReadByte() != 254)
                throw new InvalidDataException("UTF16LE_BOM_REQUIRED");
            using (StreamReader reader = new StreamReader(input, new UnicodeEncoding(false, true, true), false))
            {
                string line;
                while ((line = reader.ReadLine()) != null)
                {
                    string path = AbsolutePath(line);
                    if (!seen.Add(path)) throw new InvalidDataException("DUPLICATE_INPUT_PATH=" + path);
                    if (String.Equals(path, output, StringComparison.OrdinalIgnoreCase))
                        throw new InvalidDataException("OUTPUT_CANNOT_BE_INPUT");
                    paths.Add(path);
                }
            }
        }
        if (paths.Count == 0) throw new InvalidDataException("EMPTY_MANIFEST");
        return paths.ToArray();
    }

    private static void CheckVector(byte[] data, string expected)
    {
        using (SHA256 sha = SHA256.Create())
        {
            if (sha == null || !String.Equals(Hex(sha.ComputeHash(data)), expected, StringComparison.Ordinal))
                throw new InvalidOperationException("SHA256_SELF_TEST_FAILED");
        }
    }

    private static void SelfTest()
    {
        CheckVector(new byte[0], "e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855");
        CheckVector(Encoding.ASCII.GetBytes("abc"),
            "ba7816bf8f01cfea414140de5dae2223b00361a396177a9cb410ff61f20015ad");
        CheckVector(Encoding.ASCII.GetBytes("abcdbcdecdefdefgefghfghighijhijkijkljklmklmnlmnomnopnopq"),
            "248d6a61d20638b8e5c026930c3e6039a33ce45964ff2167f6ecedd419db06c1");
        byte[] binary = new byte[256];
        for (int i = 0; i < binary.Length; i++) binary[i] = (byte)i;
        CheckVector(binary, "40aff2e9d2d8922e47afd4648e6967497158785fbd1da870e7110266bf944880");
        byte[] million = new byte[1000000];
        for (int i = 0; i < million.Length; i++) million[i] = (byte)'a';
        CheckVector(million, "cdc76e5c9914fb9281a1c7e284d73e67f1809a48a497200e046d39ccc7112cd0");
    }

    private static int Main(string[] args)
    {
        string temporary = null;
        try
        {
            if (args.Length == 1 && args[0] == "--self-test")
            {
                SelfTest();
                Console.WriteLine("HASH_SELF_TEST=PASS");
                return 0;
            }
            if (args.Length != 3)
                throw new ArgumentException("EXPECTED_MANIFEST_OUTPUT_WORKERS");
            int workerCount;
            if (!Int32.TryParse(args[2], NumberStyles.None, CultureInfo.InvariantCulture, out workerCount)
                || workerCount < 1 || workerCount > 16)
                throw new ArgumentException("WORKERS_MUST_BE_1_TO_16");
            string manifest = AbsolutePath(args[0]);
            string output = AbsolutePath(args[1]);
            if (String.Equals(manifest, output, StringComparison.OrdinalIgnoreCase))
                throw new ArgumentException("MANIFEST_CANNOT_BE_OUTPUT");
            if (File.Exists(output) || Directory.Exists(output))
                throw new IOException("OUTPUT_ALREADY_EXISTS");
            string[] paths = ReadManifest(manifest, output);
            SelfTest();
            Batch batch = new Batch(paths);
            Thread[] workers = new Thread[Math.Min(workerCount, paths.Length)];
            for (int i = 0; i < workers.Length; i++)
            {
                workers[i] = new Thread(new ThreadStart(batch.Work));
                workers[i].IsBackground = true;
                workers[i].Start();
            }
            for (int i = 0; i < workers.Length; i++) workers[i].Join();
            if (batch.Failure != null) throw new IOException(batch.Failure);
            if (batch.Completed != paths.Length) throw new IOException("INCOMPLETE_BATCH");
            temporary = output + ".tmp." + Guid.NewGuid().ToString("N");
            using (FileStream destination = new FileStream(temporary, FileMode.CreateNew,
                FileAccess.Write, FileShare.None))
            using (StreamWriter writer = new StreamWriter(destination, Encoding.ASCII))
            {
                for (int i = 0; i < paths.Length; i++)
                {
                    if (batch.Hashes[i] == null || batch.Hashes[i].Length != 64)
                        throw new IOException("MISSING_DIGEST");
                    writer.Write(i.ToString(CultureInfo.InvariantCulture));
                    writer.Write('\t');
                    writer.WriteLine(batch.Hashes[i]);
                }
            }
            File.Move(temporary, output);
            temporary = null;
            Console.WriteLine("HASH_BATCH_PASS=" + paths.Length.ToString(CultureInfo.InvariantCulture));
            return 0;
        }
        catch (Exception error)
        {
            if (temporary != null)
            {
                try { File.Delete(temporary); } catch (Exception) { }
            }
            Console.WriteLine("HASH_BATCH_FAIL=" + ErrorText(error));
            return 1;
        }
    }
}
