const CACHE = 'spf-v1';
const OFFLINE_URLS = ['/client/dashboard', '/static/IMAGE/logo.png', '/static/IMAGE/favicon.png'];

self.addEventListener('install', e => {
  e.waitUntil(caches.open(CACHE).then(c => c.addAll(OFFLINE_URLS)).catch(() => {}));
  self.skipWaiting();
});

self.addEventListener('activate', e => {
  e.waitUntil(caches.keys().then(keys =>
    Promise.all(keys.filter(k => k !== CACHE).map(k => caches.delete(k)))
  ));
  self.clients.claim();
});

self.addEventListener('fetch', e => {
  if (e.request.method !== 'GET') return;
  const url = new URL(e.request.url);
  if (url.origin !== self.location.origin) return;
  e.respondWith(
    (async () => {
      const preload = await e.preloadResponse;
      const res = preload || await fetch(e.request).catch(() => null);
      if (res && res.status === 200) {
        const clone = res.clone();
        caches.open(CACHE).then(c => c.put(e.request, clone));
        return res;
      }
      return caches.match(e.request).then(cached => cached || res || Response.error());
    })()
  );
});

self.addEventListener('push', e => {
  const data = e.data ? e.data.json() : {};
  const title = data.title || 'Sahil Panwar Fitness';
  const opts = {
    body: data.body || 'You have a new notification',
    icon: '/static/IMAGE/favicon.png',
    badge: '/static/IMAGE/favicon.png',
    tag: data.tag || 'spf-notif',
    data: { url: data.url || '/client/dashboard' },
    vibrate: [200, 100, 200],
    requireInteraction: data.requireInteraction || false,
  };
  e.waitUntil(self.registration.showNotification(title, opts));
});

self.addEventListener('notificationclick', e => {
  e.notification.close();
  const url = (e.notification.data && e.notification.data.url) || '/client/dashboard';
  e.waitUntil(clients.matchAll({ type: 'window', includeUncontrolled: true }).then(wins => {
    for (const w of wins) {
      if (w.url.includes(url) && 'focus' in w) return w.focus();
    }
    if (clients.openWindow) return clients.openWindow(url);
  }));
});
