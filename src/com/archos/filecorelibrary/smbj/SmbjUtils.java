// Copyright 2023 Courville Software
//
// Licensed under the Apache License, Version 2.0 (the "License");
// you may not use this file except in compliance with the License.
// You may obtain a copy of the License at
//
//      http://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software
// distributed under the License is distributed on an "AS IS" BASIS,
// WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
// See the License for the specific language governing permissions and
// limitations under the License.

package com.archos.filecorelibrary.smbj;

import static com.archos.filecorelibrary.FileUtils.getShareName;

import android.content.Context;
import android.net.Uri;

import androidx.preference.PreferenceManager;

import com.archos.filecorelibrary.jcifs.JcifsUtils;
import com.archos.filecorelibrary.samba.NetworkCredentialsDatabase;
import com.archos.filecorelibrary.samba.SambaDiscovery;

import com.hierynomus.msfscc.FileAttributes;
import com.hierynomus.msfscc.fileinformation.FileIdBothDirectoryInformation;

import com.hierynomus.mserref.NtStatus;
import com.hierynomus.mssmb2.SMB2Dialect;
import com.hierynomus.mssmb2.SMBApiException;
import com.hierynomus.protocol.commons.EnumWithValue;
import com.hierynomus.protocol.transport.TransportException;
import com.hierynomus.security.bc.BCSecurityProvider;
import com.hierynomus.smbj.SMBClient;
import com.hierynomus.smbj.SmbConfig;
import com.hierynomus.smbj.auth.AuthenticationContext;
import com.hierynomus.smbj.common.SMBRuntimeException;
import com.hierynomus.smbj.connection.Connection;
import com.hierynomus.smbj.session.Session;
import com.hierynomus.smbj.share.DiskShare;

import org.slf4j.Logger;
import org.slf4j.LoggerFactory;

import java.io.IOException;
import java.net.SocketException;
import java.util.concurrent.ConcurrentHashMap;
import java.util.concurrent.locks.ReentrantReadWriteLock;
import java.util.function.Predicate;

public class SmbjUtils {

    private static final Logger log = LoggerFactory.getLogger(SmbjUtils.class);
    static private ConcurrentHashMap<NetworkCredentialsDatabase.Credential, Session> smbjSessions = new ConcurrentHashMap<>();
    static private ConcurrentHashMap<NetworkCredentialsDatabase.Credential, DiskShare> smbjShares = new ConcurrentHashMap<>();
    static private ConcurrentHashMap<NetworkCredentialsDatabase.Credential, Connection> smbjConnections = new ConcurrentHashMap<>();
    // Guards the share/session/connection for a given credential against being torn down by
    // resetConnection() while another thread is still actively using it (see withRetry/withReadRetry):
    // readers (actual SMB operations) hold the read lock for the duration of the call, resetConnection()
    // takes the write lock, so a share can never be closed underneath an in-flight operation.
    static private final ConcurrentHashMap<NetworkCredentialsDatabase.Credential, ReentrantReadWriteLock> smbjShareLocks = new ConcurrentHashMap<>();
    private static Context mContext;
    // singleton, volatile to make double-checked-locking work correctly
    private static volatile SmbjUtils sInstance;

    private static SmbConfig smbConfig;
    // Connection attempts, in the same order as the Proshektor app, which is known to work with routers that
    // close the connection on the SMB1 "multi-protocol" negotiate packet that smbj uses by default:
    //  1) direct SMB2 negotiation, dialects 2.1 and 3.0
    //  2) direct SMB2 negotiation, all dialects
    //  3) multi-protocol negotiation (historical behavior)
    private static java.util.List<SmbConfig> smbConnectConfigs;
    // which attempt worked for a given server (resolved IP + port): tried first next time
    private static final java.util.Map<String, Integer> smbConfigIndexByServer = new ConcurrentHashMap<>();

    // get the instance, context is used for initial context injection
    public static SmbjUtils getInstance(Context context) {
        if (context == null) log.warn("getInstance: context passed is null!!!");
        else if (mContext == null) mContext = context;
        if (sInstance == null) {
            synchronized(SmbjUtils.class) {
                if (sInstance == null) sInstance = new SmbjUtils(context.getApplicationContext());
            }
        }
        return sInstance;
    }

    /** may return null but no Context required */
    public static SmbjUtils peekInstance() {
        return sInstance;
    }

    @FunctionalInterface
    public interface CheckedSupplier<T> {
        T get() throws Exception;
    }

    private SmbjUtils(Context context) {
        mContext = context;
        if (log.isDebugEnabled()) log.debug("SmbjUtils: initializing contexts");
        smbConfig = SmbConfig.builder()
                .withSecurityProvider(new BCSecurityProvider())
                .withMultiProtocolNegotiate(true)
                .withSigningRequired(false)
                .build();
        SmbConfig direct21and30 = SmbConfig.builder()
                .withSecurityProvider(new BCSecurityProvider())
                .withMultiProtocolNegotiate(false)
                .withDialects(SMB2Dialect.SMB_2_1, SMB2Dialect.SMB_3_0)
                .withSigningRequired(false)
                .build();
        SmbConfig directAllDialects = SmbConfig.builder()
                .withSecurityProvider(new BCSecurityProvider())
                .withMultiProtocolNegotiate(false)
                .withSigningRequired(false)
                .build();
        smbConnectConfigs = java.util.Arrays.asList(direct21and30, directAllDialects, smbConfig);
    }

    /**
     * Opens the TCP/SMB connection to the server, trying the configurations of {@link #smbConnectConfigs} in
     * order (the one that worked last time for this server goes first). A failure to reach the host at all is
     * not retried with another dialect.
     */
    private Connection connectToServer(String serverIP, int port) throws IOException {
        final String key = serverIP + ":" + (port != -1 ? port : 445);
        final int n = smbConnectConfigs.size();
        final Integer known = smbConfigIndexByServer.get(key);
        final int[] order = new int[n];
        int k = 0;
        if (known != null && known >= 0 && known < n) order[k++] = known;
        for (int i = 0; i < n; i++) {
            if (known == null || i != known) order[k++] = i;
        }
        Exception last = null;
        for (int idx : order) {
            SMBClient client = new SMBClient(smbConnectConfigs.get(idx));
            try {
                Connection c = (port != -1) ? client.connect(serverIP, port) : client.connect(serverIP);
                smbConfigIndexByServer.put(key, idx);
                if (log.isDebugEnabled()) log.debug("connectToServer: {} connected with configuration #{}", key, idx);
                return c;
            } catch (Exception e) {
                try {
                    client.close();
                } catch (Exception ignored) {
                    // nothing to do
                }
                log.warn("connectToServer: configuration #{} failed for {}: {}", idx, key, e.toString());
                if (last != null) e.addSuppressed(last);
                last = e;
                if (isHostUnreachable(e)) break; // another dialect will not help
            }
        }
        smbConfigIndexByServer.remove(key);
        throw asIOException(last != null ? last : new IOException("Unable to connect to " + key));
    }

    private static boolean isHostUnreachable(Throwable e) {
        for (Throwable t = e; t != null; t = t.getCause()) {
            if (t instanceof java.net.ConnectException
                    || t instanceof java.net.NoRouteToHostException
                    || t instanceof java.net.UnknownHostException) {
                return true;
            }
            if (t.getCause() == t) break;
        }
        return false;
    }

    private static IOException asIOException(Exception e) {
        return (e instanceof IOException) ? (IOException) e : new IOException(e);
    }

    public int getReadBufferSize() {
        return smbConfig.getReadBufferSize();
    }

    public long getReadTimeout() {
        return smbConfig.getReadTimeout();
    }

    public synchronized void getSmbConnection(Uri uri) throws IOException, SMBApiException {
        NetworkCredentialsDatabase.Credential cred = NetworkCredentialsDatabase.getInstance().getCredential(uri.toString());
        if (cred == null)
            cred = new NetworkCredentialsDatabase.Credential("anonymous", "", buildKeyFromUri(uri).toString(), "", true);
        String server = uri.getHost();
        String password = cred.getPassword();
        String username = cred.getUsername();
        String domain = cred.getDomain();
        int port = uri.getPort();
        Connection smbConnection = smbjConnections.get(cred);
        // a connection can be TCP-connected yet have no authenticated session if a previous
        // authenticate() call failed (e.g. STATUS_ACCESS_DENIED for another share on the same
        // server): treat that as needing a fresh connection/authentication too, otherwise every
        // subsequent call for this cred silently skips authentication forever (session stays null)
        if (smbConnection == null || !smbConnection.isConnected() || smbjSessions.get(cred) == null) {
            if (log.isTraceEnabled()) log.trace("getSmbConnection: smbConnection is null, not connected or has no session for {}, connecting to {}", uri, server);
            if (smbConnection != null) {
                try {
                    smbConnection.close(true);
                } catch (Exception e) {
                    log.warn("getSmbConnection: failed closing stale connection for {}: {}", uri, e.getMessage());
                }
                smbjConnections.remove(cred, smbConnection);
                smbjSessions.remove(cred);
            }
            String serverIP = SambaDiscovery.getIpFromShareName(server);
            if (serverIP == null)
                serverIP = JcifsUtils.getInstance(mContext).getBaseContextOnly(true).getNameServiceClient().getByName(server).getHostAddress();
            if (log.isTraceEnabled()) log.trace("getSmbConnection: {} -> {}", server, serverIP);
            smbConnection = connectToServer(serverIP, port);
            smbjConnections.put(cred, smbConnection);
            if (password == null) {
                password = "";
            }
            if (username == null) {
                username = "";
            } else {
                int ci = username.indexOf('@');
                if (ci > 0) {
                    domain = username.substring(ci + 1);
                    username = username.substring(0, ci);
                } else {
                    ci = username.indexOf('\\');
                    if (ci > 0) {
                        domain = username.substring(0, ci);
                        username = username.substring(ci + 1);
                    }
                }
            }
            // need to regenerate smbSession in this case too
            AuthenticationContext ac;
            if ((username.isEmpty() || "guest".equalsIgnoreCase(username) || "anonymous".equalsIgnoreCase(username))
                    && password.isEmpty()) {
                ac = AuthenticationContext.guest();
            } else {
                ac = new AuthenticationContext(username, password.toCharArray(), domain);
            }
            if (ac == null) {
                log.error("getSmbConnection: AuthenticationContext is null for uri {}", uri);
                throw new IOException("Failed to create AuthenticationContext");
            }
            Session smbSession;
            try {
                smbSession = smbConnection.authenticate(ac);
            } catch (SMBRuntimeException e) {
                // authentication failed (e.g. SMB2GuestSigningRequiredException, STATUS_ACCESS_DENIED,
                // STATUS_LOGON_FAILURE): drop the connection so we don't leave a connected-but-
                // unauthenticated entry cached that would silently skip re-authentication next time
                log.error("getSmbConnection: caught {} authenticating for uri {} -> dropping connection", e.getClass().getSimpleName(), uri, e);
                smbjConnections.remove(cred, smbConnection);
                try {
                    smbConnection.close(true);
                } catch (Exception ce) {
                    log.warn("getSmbConnection: failed closing connection after auth failure for {}: {}", uri, ce.getMessage());
                }
                throw e;
            }
            smbjSessions.put(cred, smbSession);
        }
    }

    /**
     * Reset cached share/session/connection for a URI and close existing resources.
     */
    public synchronized void resetConnection(Uri uri) {
        NetworkCredentialsDatabase.Credential cred = NetworkCredentialsDatabase.getInstance().getCredential(uri.toString());
        if (cred == null)
            cred = new NetworkCredentialsDatabase.Credential("anonymous", "", buildKeyFromUri(uri).toString(), "", true);
        DiskShare share = smbjShares.remove(cred);
        if (share != null) {
            try {
                share.close();
            } catch (Exception e) {
                log.warn("resetConnection: failed closing share for {}: {}", uri, e.getMessage());
            }
        }
        Session session = smbjSessions.remove(cred);
        if (session != null) {
            try {
                session.close();
            } catch (Exception e) {
                log.warn("resetConnection: failed closing session for {}: {}", uri, e.getMessage());
            }
        }
        Connection connection = smbjConnections.remove(cred);
        if (connection != null) {
            try {
                connection.close(true);
            } catch (Exception e) {
                log.warn("resetConnection: failed closing connection for {}: {}", uri, e.getMessage());
            }
        }
    }

    private boolean isOutOfCredits(Throwable t) {
        Throwable current = t;
        while (current != null) {
            if (current instanceof SMBRuntimeException && current.getMessage() != null &&
                    current.getMessage().contains("Not enough credits")) {
                return true;
            }
            current = current.getCause();
        }
        return false;
    }

    private boolean isTransportError(Throwable t) {
        Throwable current = t;
        while (current != null) {
            if (current instanceof TransportException || current instanceof SocketException || current instanceof java.io.EOFException) {
                return true;
            }
            if (current instanceof SMBRuntimeException && current.getCause() != null) {
                if (current.getCause() instanceof TransportException || current.getCause() instanceof SocketException || current.getCause() instanceof java.io.EOFException) {
                    return true;
                }
            }
            current = current.getCause();
        }
        return false;
    }

    /**
     * Execute an SMBJ operation, resetting the connection and retrying once if the server reports
     * that we ran out of credits. Safe for all operations (including mutating ones).
     */
    public <T> T withRetry(Uri uri, CheckedSupplier<T> supplier) throws Exception {
        return executeWithRetry(uri, supplier, this::isOutOfCredits, "withRetry");
    }

    /**
     * Execute an SMBJ operation, resetting the connection and retrying once if the server reports
     * that we ran out of credits or if a transport error occurred.
     * ONLY use this for idempotent operations (directory listing, exists, etc.).
     */
    public <T> T withReadRetry(Uri uri, CheckedSupplier<T> supplier) throws Exception {
        return executeWithRetry(uri, supplier, this::isRetryableReadError, "withReadRetry");
    }

    /**
     * Runs supplier while holding the per-credential read lock, so resetConnection() (which
     * physically closes the cached share/session/connection) cannot run concurrently with it: two
     * threads can both be reading at once, but a reset always waits for every in-flight reader to
     * finish first, and no new reader can start while a reset is in progress. Without this, one
     * thread's retry-triggered resetConnection() could close a DiskShare that another thread was
     * still actively using, surfacing as "DiskShare has already been closed" in the middle of an
     * unrelated listing/exists/read call.
     */
    private <T> T executeWithRetry(Uri uri, CheckedSupplier<T> supplier, Predicate<Exception> isRetryable, String tag) throws Exception {
        ReentrantReadWriteLock lock = lockFor(uri);
        Exception firstError;
        lock.readLock().lock();
        try {
            return supplier.get();
        } catch (Exception e) {
            firstError = e;
        } finally {
            lock.readLock().unlock();
        }
        if (!isRetryable.test(firstError)) throw firstError;
        log.warn("{}: error (out of credits or transport) for {}, resetting connection and retrying", tag, uri, firstError);
        // must not hold the read lock while resetting (a thread cannot upgrade its own read lock to
        // a write lock without releasing it first, that would deadlock waiting on itself)
        lock.writeLock().lock();
        try {
            resetConnection(uri);
        } finally {
            lock.writeLock().unlock();
        }
        lock.readLock().lock();
        try {
            return supplier.get();
        } finally {
            lock.readLock().unlock();
        }
    }

    private ReentrantReadWriteLock lockFor(Uri uri) {
        NetworkCredentialsDatabase.Credential cred = NetworkCredentialsDatabase.getInstance().getCredential(uri.toString());
        if (cred == null)
            cred = new NetworkCredentialsDatabase.Credential("anonymous", "", buildKeyFromUri(uri).toString(), "", true);
        return smbjShareLocks.computeIfAbsent(cred, c -> new ReentrantReadWriteLock());
    }

    public boolean isRetryableReadError(Throwable t) {
        if (isOutOfCredits(t) || isTransportError(t)) {
            return true;
        }
        Throwable current = t;
        while (current != null) {
            if (current instanceof SMBApiException) {
                NtStatus status = ((SMBApiException) current).getStatus();
                if (status == NtStatus.STATUS_INTERNAL_ERROR
                        || status == NtStatus.STATUS_FILE_CLOSED
                        || status == NtStatus.STATUS_CONNECTION_DISCONNECTED
                        || status == NtStatus.STATUS_CONNECTION_RESET
                        || status == NtStatus.STATUS_NETWORK_NAME_DELETED
                        || status == NtStatus.STATUS_NETWORK_SESSION_EXPIRED
                        || status == NtStatus.STATUS_USER_SESSION_DELETED) {
                    return true;
                }
            }
            current = current.getCause();
        }
        return false;
    }


    public synchronized DiskShare getSmbShare(Uri uri) throws IOException, SMBApiException {
        NetworkCredentialsDatabase.Credential cred = NetworkCredentialsDatabase.getInstance().getCredential(uri.toString());
        if (cred == null)
            cred = new NetworkCredentialsDatabase.Credential("anonymous", "", buildKeyFromUri(uri).toString(), "", true);
        String shareName = getShareName(uri);
        getSmbConnection(uri); // be sure to be connected
        // shareName can be null when asking for smbj://server/
        if (shareName == null) {
            log.warn("getSmbShare: returning null shareName for uri {}", uri);
            throw new IOException("Cannot connect to SMB share: share name is missing or null for " + uri);
        }
        DiskShare smbShare = smbjShares.get(cred);
        if (smbShare == null || !shareName.equals(getShareName(Uri.parse(cred.getUriString()))) || !smbShare.isConnected()) {
            if (log.isTraceEnabled()) log.trace("getSmbShare: smbShare is null or not connected for {}", shareName);
            // ensures that there is a valid connection and regenerate session if not connected
            getSmbConnection(uri);
            Session smbSession = smbjSessions.get(cred);
            if (smbSession != null) {
                try {
                    smbShare = (DiskShare) smbSession.connectShare(shareName);
                    if (log.isTraceEnabled()) log.trace("getSmbShare: saving smbShare {}, smbshare={}", shareName, smbShare);
                    smbjShares.put(cred, smbShare);
                } catch (SMBRuntimeException e) {
                    if (e instanceof SMBApiException) {
                        throw (SMBApiException) e;
                    }
                    if (e.getCause() instanceof SocketException) {
                        // Try to reconnect
                        getSmbConnection(uri);
                        smbSession = smbjSessions.get(cred);
                        if (smbSession != null) {
                            smbShare = (DiskShare) smbSession.connectShare(shareName);
                            smbjShares.put(cred, smbShare);
                        } else {
                            log.error("getSmbShare: caught SMBRuntimeException but smbSession is null after reconnecting! {} for uri {}, sharename={} -> throwing IOException instead", e.getMessage(), uri, shareName);
                            throw new IOException("getSmbShare: smbSession is null after reconnecting!", e);
                        }
                    } else {
                        log.error("getSmbShare: caught exception {} for uri {}, sharename={} -> throwing IOException instead", e.getMessage(), uri, shareName);
                        throw new IOException("getSmbShare: caught SMBRuntimeException", e);
                    }
                }
            } else log.warn("getSmbShare: smbSession is null!");
        }
        if (log.isDebugEnabled()) log.debug("getSmbShare: for uri {}, sharename={}, smbShare={}, isConnected={}", uri, shareName, smbShare, (smbShare != null)?smbShare.isConnected():"false");
        if (smbShare == null) {
            log.error("getSmbShare: smbShare is null for uri {}, sharename={}", uri, shareName);
            throw new IOException("Failed to connect to SMB share: " + shareName + " for " + uri);
        }
        return smbShare;
    }

    private static Uri buildKeyFromUri(Uri uri) {
        // use Uri without the path segment as key: for example, "smbj://blabla.com:5006/toto/titi" gives a "smbj://blabla.com:5006" key
        return uri.buildUpon().path("").build();
    }

    public static boolean isDirectory(FileIdBothDirectoryInformation fileEntry) {
        return EnumWithValue.EnumUtils.isSet(fileEntry.getFileAttributes(), FileAttributes.FILE_ATTRIBUTE_DIRECTORY);
    }

    // smbj is the SMB client of this build (it can negotiate SMB2 directly, which jcifs-ng cannot do against routers
    // that cut the multi-protocol negotiation). A dedicated key is used so that neither the old "pref_smbj" value
    // stored on the device nor Nova's upgrade migration (which forces "pref_smbj" to false) can turn it off.
    private static final String SMBJ_PREF_KEY = "pref_smbj_smbfix";

    public static boolean isSMBjEnabled() {
        if (mContext == null) {
            log.error("isSMBjEnabled: mContext is null! Returning false");
            return false;
        }
        if (log.isTraceEnabled()) log.trace("isSMBjEnabled={}", PreferenceManager.getDefaultSharedPreferences(mContext).getBoolean(SMBJ_PREF_KEY, true));
        return PreferenceManager.getDefaultSharedPreferences(mContext).getBoolean(SMBJ_PREF_KEY, true);
    }

    /**
     * Invalidate cached DiskShare for a URI, forcing reconnection on next access.
     * Used when a protocol error (TransportException) indicates connection is compromised.
     */
    public synchronized void invalidateShare(Uri uri) {
        NetworkCredentialsDatabase.Credential cred = NetworkCredentialsDatabase.getInstance().getCredential(uri.toString());
        if (cred != null) {
            DiskShare share = smbjShares.remove(cred);
            if (share != null) {
                if (log.isDebugEnabled()) log.debug("invalidateShare: removed cached share for {}", uri);
            }
        }
    }

}
